from sympy import *
a1,a2,b1,b2,c1,c2,p1,p2=symbols('a1 a2 b1 b2 c1 c2 p1 p2')
def foot(p,u,v):
    d=(v[0]-u[0],v[1]-u[1]); N=(p[0]-u[0])*d[0]+(p[1]-u[1])*d[1]; D=d[0]**2+d[1]**2
    return (u[0]*D+N*d[0], u[1]*D+N*d[1], D)  # homogeneous: foot = (X/D, Y/D)
A=(a1,a2);B=(b1,b2);C=(c1,c2);P=(p1,p2)
F=[foot(P,B,C),foot(P,C,A),foot(P,A,B)]
M=Matrix([[f[0],f[1],f[2]] for f in F])
Q=expand(M.det())
gs=[a1**2+a2**2-p1**2-p2**2,b1**2+b2**2-p1**2-p2**2,c1**2+c2**2-p1**2-p2**2]
qs,r=reduced(Q,gs,a1,b1,c1,a2,b2,c2,p1,p2,order='lex')
print("rem",r); 
for q in qs: print(len(str(factor(q))), factor(q))
