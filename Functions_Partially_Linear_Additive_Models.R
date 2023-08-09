simdata <- function(n,no.cov,CL) {
  
  if(no.cov == 2){
    t<-0
    z <- 0
    x<-matrix(c(runif(n),runif(n)),n,2)
    for (j in 1:n){
      t[j]<-(j-0.5)/n
    }
    t2<-sort(runif(n,min=-2,max=2))
    f1<-1-48*t+218*t^2-315*t^3+145*t^4
    f2<-exp(t2)-2*sin(t2)
    beta<-c(1,-0.5)
    error<-rnorm(n,sd=0.3)
    y<-x%*%beta+f1+f2+error
    delta <- rbinom(n,1,(1-CL))
    for (j in 1:n){
      if (delta[j]==0){
        z[j] <- y[j]-abs(rnorm(1,sd=sd(y)))
      }
      else{
        z[j] <- y[j]
      }
    }
    
    nc<-matrix(c(t,t2),n,2)
    allf<-matrix(c(f1,f2),n,2)
    dat<-new.env()
    dat$x<-x
    dat$y<-y
    dat$z<-z
    dat$delta <- delta
    dat$nc<-nc
    dat$beta<-beta
    dat$allf<-allf
  } 
  return(dat)
}
knnimp  <-function(x,y,K,delta){
  
  dist<-NA
  index<-NA
  knny<-NA
  y2<-NA
  t2<-0
  a<-NA
  n<-length(y)
  
  say<-0
  for (i2 in 1:n) {
    if (delta[i2]==0){
      for (j in 1:n){
        dist[j]<-(y[i2]-y[j])^2
        index[j]<-j
        if (dist[j]==0){
          dist[j]<-NA
          index[j]<-NA
        }
      }
      say<-say+1
      dist<- dist[!is.na(dist)]
      index<- index[!is.na(index)]
      disted<-matrix(c(index,dist),length(index),2)
      sdist<-sortrows(disted,k=2)
      for (t in 1:length(dist)){
        a[t]<-sdist[t,1]
        
      }
      for (j2 in 1:length(a)){
        if (is.na(y[a[j2]])){
          a[j2]<-NA
        }
      }
      a<- a[!is.na(a)]
      for (t2 in 1:K){
        knny[t2]<-y[a[t2]]
      }
      y2[i2]<-mean(knny)+std(y)/1.5
    }
    
  }
  for (h in 1:n){
    if (delta[h]==0){
      y[h]<-y2[h]
    }
  }
  return(y)
}
zerone  <- function(x){
  xnew <- (x-min(x))/(max(x)-min(x))
}
syndata <-function(y,delta){
  library(pracma)
  # where y: right-censored observations, delta: censorship indicator
  n<-length(y)
  M<-0
  yg<-0
  M<-0
  delta2<-0
  #Synthetic data transformation
  y1<-cbind(y,delta)
  y2<-sortrows(y1,k=2)
  delta2<-y2[,2]
  delta2[n]<-1
  sy<-sort(y)
  for (i1 in 1:n){
    Ma<-1
    for (i2 in 1:n){
      mGt<-((n-i2)/(n-i2+1))^((delta2[i2]==0)*(sy[i2]<=sy[i1]))
      Ma<-Ma*mGt
    }
    M[i1]=Ma
    yg[i1]<-(delta[i1]*y[i1])/M[i1]
  }
  return(yg)
}
SPAMLL  <-function(x,y,nc,allf,no.iter){
  library(optR)
  library(psych)
  library(pracma)
  library(KernSmooth)
  library(locfit)
  library(evmix)
  size<-dim(nc)
  q<-size[2]
  #-------Improved AIC (AICc)----------
  #----------------------------------
  K<-function(z){
    res<-(1/sqrt(2*pi))*exp(-0.5*z^2)
    return(res)
  }
  #------------------------------------
  
  if (q==2){
    #x: matrix of parametric covariates
    #y: response variable
    #nc: Matrix of nonparamtric covariate
    f1<-(allf[,1])
    f2<-(allf[,2])
    n<-length(y)
    z1<-(nc[,1])     # After Revision 3
    z2<-(nc[,2])     # After Revision 3
    x <- (x)
    #BACKFITTING PROCEDURE----------------------------------------------------
    #Initialization-----------------------------------------------------------
    #f01 <- fitted(lm(y~z1+x[,1]+x[,2]))
    #f02 <- fitted(lm(y~z2+x[,1]+x[,2]))
    
    f02 <- (predict(loess(y~z2)))
    f01 <- (predict(loess((y)~z1)))
    
    #SMOOTHING MATRIX FOR KS--------------------------------------------------
    Smat<-function(z,bw){
      library(condSURV)
      K<-function(z){
        res<-(1/sqrt(2*pi))*exp(-0.5*z^2)
        return(res)
      }
      n<-length(z)
      za<-seq(min(z),max(z),length.out = n)
      W  <- matrix(0,n,n)
      Sr  <- matrix(0,n,n)
      for (i in 1:n){
        d  <- matrix(c(1,0),2,1)
        Zr <- matrix(c(matrix(1,n,1),za-z[i]),n,2)
        u<-(za-z[i])/bw
        Wdiag <- K(u)
        Wr<-diag(Wdiag)
        Sr[,i]<-t(d)%*%solve(t(Zr)%*%Wr%*%Zr,tol=1e-100)%*%t(Zr)%*%Wr
      }
      SLL <- Sr
      return(SLL)
    }
    #-----------------------------------------------------------------------------
    selectionLL <- function(x,z,y){
      gcv <- 0
      #---------------GCV-----------------
      gcvfunc<-function(y,yhat,H){
        y<-matrix(c(y))
        yhat<-matrix(c(yhat))
        n<-length(y)
        score<-(1/n)*(norm(y-yhat)^2)/(((1/n)*tr(diag(n)-H))^2)
        return(score)
      }
      #---------------GCV-----------------
      #-----------------------------------------------------------------------------
      Smat<-function(z,bw){
        library(condSURV)
        K<-function(z){
          res<-(1/sqrt(2*pi))*exp(-0.5*z^2)
          return(res)
        }
        n<-length(z)
        za<-seq(min(z),max(z),length.out = n)
        W  <- matrix(0,n,n)
        Sr  <- matrix(0,n,n)
        for (i in 1:n){
          d  <- matrix(c(1,0),2,1)
          Zr <- matrix(c(matrix(1,n,1),za-z[i]),n,2)
          u<-(za-z[i])/bw
          Wdiag <- K(u)
          Wr<-diag(Wdiag)
          Sr[,i]<-t(d)%*%solve(t(Zr)%*%Wr%*%Zr,tol=1e-100)%*%t(Zr)%*%Wr
        }
        SLL <- Sr
        return(SLL)
      }
      n      <- length(y)
      index  <-seq(min(z)-0.1,max(z)+0.1,length.out=n)
      tp_seq <-seq(0.2,1,length.out=20)
      for (i in 1:20){
        W    <- Smat(z,tp_seq[i]) 
        xtil <- (diag(n)-W)%*%x
        ytil <- (diag(n)-W)%*%y
        
        beta <- solve(t(xtil)%*%xtil)%*%t(xtil)%*%ytil
        fhat <- W%*%(y-x%*%beta)
        yhat <- x%*%beta+fhat
        H    <- W+xtil%*%solve(t(xtil)%*%xtil)%*%t(x)%*%(diag(n)-W)^2
        gcv[i] <- gcvfunc(y,yhat,H)
      }
      
      for (i2 in 1:20){
        if (gcv[i2]==min(gcv)){
          lam_gcv <- tp_seq[i2]
        }
      }
      res <- new.env()
      res$lam.gcv <- lam_gcv
      res$gcvscore <- gcv
      return(res)
    }
    #BACKFITTING BEGINS-------------------------------------------------------
    #-------------------------------------------------------------------------
    alpha0 <- mean(y)
    
    fhat1_gcv <- matrix(0,n,1)
    fhat2_gcv <- matrix(0,n,1)
    
    fhat_gcv <- matrix(c(f01,f02),n,2)
    #fhat_gcv <- matrix(0,n,2)
    iter <- no.iter
    
    fh1_gcv <-matrix(0,n,iter)
    fh2_gcv <- matrix(0,n,iter)
    
    tol    <- 0.05
    ctol   <- 99
    yhat      <- 0
    i      <- 1
    while (ctol>=tol){
      for (k in 1:2){
        yresid <- y-yhat
        tp <- selectionLL(x,nc[,k],(y))
        tp.gcv <- tp$lam.gcv
        S_gcv  <- Smat((nc[,k]),tp.gcv)
        ones <- matrix(1,n,1)
        xa <- matrix(c(ones,x),n,3)
        xtil.gcv <- (diag(n)-S_gcv)%*%x
        ytil.gcv <- (diag(n)-S_gcv)%*%y
        
        H.gcv <- S_gcv+xtil.gcv%*%solve(t(xtil.gcv)%*%xtil.gcv)%*%t(x)%*%(diag(n)-S_gcv)^2
        
        betai_gcv   <- solve(t(x)%*%x)%*%t(x)%*%(y-alpha0-(fhat_gcv[,k]+fhat_gcv[,-k]))
        #fhat_gcv[,k]<- S_gcv%*%(y-alpha0-(x%*%betai_gcv)-fhat_gcv[,-k])
        fresid<- (y-alpha0-(x%*%betai_gcv)-fhat_gcv[,-k])
        fhat_gcv[,k]<- predict(loess(fresid~nc[,k],span=tp.gcv))
        
        
        yhat <- alpha0-x%*%betai_gcv-fhat_gcv[,k]-fhat_gcv[,-k]
        
        #par(mfrow=c(1,2))
        #plot(fhat_gcv[,1],type="l")
        #plot(fhat_gcv[,2],type="l")
        if (k==1){
          GCV.f1     <- tp$gcvscore
          fhat1_gcv  <- fhat_gcv[,k]
          fh1_gcv[,i]<- fhat1_gcv
        }
        if (k==2){
          GCV.f2      <- tp$gcvscore
          fhat2_gcv   <- fhat_gcv[,k]
          fh2_gcv[,i] <- fhat2_gcv
        }
        if (i>1){
          ctol <- mean(abs(y-yhat))
        }
        
      }
      i <- i+1
      if (i==iter){
        break
      }
    }
    
    GCV <- matrix(c(GCV.f1,GCV.f2),20,2)
    yhatBF_gcv <- x%*%betai_gcv+fhat1_gcv+fhat2_gcv
    
    #plot(scale(f1),pch=19,type="l")
    #par(new=TRUE)
    #plot(fhat1_aic,col="red",pch=19,type="l",ylim=c(min(f1),max(f1)))
    #lines(scale(fhat1_gcv),col="red",pch=19,type="l")
    #par(new=TRUE)
    #plot(fhat1_cp,col="red",pch=19,type="l",ylim=c(min(f1),max(f1)))
    
    #plot(scale(f2),pch=19,type="l")
    #  plot(fhat2_aic,col="red",pch=19,type="l",ylim=c(min(f2),max(f2)))
    #  par(new=TRUE)
    #lines(scale(fhat2_gcv),col="red",pch=19,type="l")
    #  par(new=TRUE)
    #  plot(fhat2_cp,col="red",pch=19,type="l",ylim=c(min(f2),max(f2)))
    
    #plot(y,pch=19,type="l",ylim=c(min(y),max(y)))
    #  par(new=TRUE)
    #  plot(yhatBF_aic,col="red",pch=19,type="l",ylim=c(min(y),max(y)))
    #  par(new=TRUE)
    #  plot(yhatBF_gcv,col="red",pch=19,type="l",ylim=c(min(y),max(y)))
    #  par(new=TRUE)
    #  plot(yhatBF_cp,col="red",pch=19,type="l",ylim=c(min(y),max(y)))
    
    
    FHAT_gcv<-matrix(c(fhat1_gcv,fhat2_gcv),n,2)
    
    ctol
  }
  ###################################################
  
  res<-new.env()
  #----------------------------------------------
  res$beta_gcv   <-betai_gcv
  res$fhat_gcv   <-FHAT_gcv
  res$fitted_gcv <-yhatBF_gcv
  res$Smat.gcv   <-S_gcv
  res$H.gcv      <-H.gcv
  res$GCV        <-GCV 
  
  return(res)
} 
censoredplots <- function(real,censored,solved,a="Nameofsolutionmethod",tit="titleoftheplot"){
  library(ggplot2)
  library(hrbrthemes)
  n     <- length(real)
  index <- seq(0,1,length.out = n)
  df1   <- data.frame(index,real)
  df2   <- data.frame(index,censored)
  df3   <- data.frame(index,solved)
  
  p <- ggplot()+geom_point(data=df1,aes(x=index,y=censored,col="Censored data"))+
    geom_point(data=df3,aes(x=index,y=solved,col=a))+
    geom_point(data=df2,aes(x=index,y=real,col="Complete data"))+
    geom_line(data=df1,aes(x=index,y=censored,col="Censored data",lty="Censoerd data"))+
    geom_line(data=df3,aes(x=index,y=solved,col=a,lty=a))+
    geom_line(data=df2,aes(x=index,y=real,col="Complete data",lty="Complete data"))+ylab("Response variable")+
    theme_minimal()+theme(legend.title = element_blank())+ggtitle(tit)
  
  return(p)
  print(p)
}