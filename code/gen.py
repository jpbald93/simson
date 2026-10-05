from sympy import *
a1,a2,b1,b2,c1,c2,p1,p2=symbols('a1 a2 b1 b2 c1 c2 p1 p2')
def foot(p,u,v):
    d=(v[0]-u[0],v[1]-u[1]); N=(p[0]-u[0])*d[0]+(p[1]-u[1])*d[1]; D=d[0]**2+d[1]**2
    return (u[0]*D+N*d[0], u[1]*D+N*d[1], D)
A=(a1,a2);B=(b1,b2);C=(c1,c2);P=(p1,p2)
F=[foot(P,B,C),foot(P,C,A),foot(P,A,B)]
Q=expand(Matrix([list(f) for f in F]).det())
gs=[a1**2+a2**2-(p1**2+p2**2),b1**2+b2**2-(p1**2+p2**2),c1**2+c2**2-(p1**2+p2**2)]
qs,r=reduced(Q,gs,a1,b1,c1,a2,b2,c2,p1,p2,order='lex'); assert r==0
assert expand(Q-sum(q*g for q,g in zip(qs,gs)))==0
L=lambda e: str(factor(e)).replace('**','^')
def fs(f): return [L(x) for x in f]
X=[fs(f) for f in F]
out=open('/home/work/Projects/simson/code/cert.lean.txt','w')
out.write("DET:="+L(Q)+"\n")
for i,q in enumerate(qs): out.write(f"Q{i}:="+L(q)+"\n")
print(len(L(Q)),[len(L(q)) for q in qs])
