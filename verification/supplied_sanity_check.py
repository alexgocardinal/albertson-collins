"""Independent finite sanity checks for proposed Albertson--Collins proof.
These checks are NOT a substitute for the all-order mathematical argument.
Uses only Python standard library.
"""
import itertools as it,json,pathlib,time
D=pathlib.Path(__file__).resolve().parent

def prime(p):return p>=2 and all(p%d for d in range(2,int(p**.5)+1))

def odd_cycle_perms(k):
    out=[]
    for p in it.permutations(range(k)):
        todo=set(range(k));valid=True
        while todo:
            u=todo.pop();v=p[u];length=1
            while v!=u:
                todo.remove(v);length+=1;v=p[v]
            if length%2==0:valid=False;break
        if valid:out.append(p)
    return out

def compatible(n,p):
    q=n//2;pa=list(range(q));rank=[0]*q;xor=[0]*q
    def find(a):
        if pa[a]!=a:
            r,z=find(pa[a]);xor[a]^=z;pa[a]=r
        return pa[a],xor[a]
    def lit(d):
        d%=n
        return (d-1,0) if d<=q else (n-d-1,1)
    for u in range(n):
        for v in range(u):
            i,b=lit(u-v);j,c=lit(p[u]-p[v]);r,a=find(i);s,z=find(j);need=b^c^a^z
            if r==s:
                if need:return False,None
            else:
                if rank[r]<rank[s]:r,s=s,r
                pa[s]=r;xor[s]=need
                if rank[r]==rank[s]:rank[r]+=1
    values=[find(i)[1] for i in range(q)]
    return True,values

def main():
    st=time.monotonic();pr=[]
    for p in range(3,1000,2):
        if not prime(p):continue
        q=p//2;m=q+1;I=set(range(m));mu=q*pow(2,-1,p)%p
        moment=sum((i-mu)**2 for i in I)%p
        assert moment!=0
        if p>3:assert moment==(-pow(32,-1,p))%p
        stabilizers=[]
        for a in range(1,p):
            b=((1-a)*mu)%p
            if {(a*i+b)%p for i in I}==I:stabilizers.append((a,b))
        assert stabilizers==[(1,0),(p-1,q)]
        pr.append({'prime':p,'moment':moment,'affine_stabilizers':stabilizers})
    blocktests=0
    for a in range(3,100,2):
        for b in range(3,100,2):
            n=a*b;I=set(range((n+1)//2));v=b//2;u=a//2
            for r in range(a):
                ts=[t for t in range(b) if r+a*t in I]
                assert ts==list(range(v+1 if r<=u else v))
                if r>u:assert [t for t in range(b) if t not in ts]==list(range(v,2*v+1))
            blocktests+=1
    ex=[]
    for n in [3,5,7,9,11,13]:
        q=n//2;left=odd_cycle_perms(q+1);right=odd_cycle_perms(q);tested=0
        identity=tuple(range(n))
        for a,b in it.product(left,right):
            p=a+tuple(x+q+1 for x in b)
            if p==identity:continue
            ok,val=compatible(n,p);tested+=1
            if ok:
                witness={'n':n,'permutation':p,'connector_bits':val}
                (D/'COUNTEREXAMPLE_TO_PROOF.json').write_text(json.dumps(witness,indent=2))
                raise AssertionError(witness)
        ex.append({'n':n,'odd_order_color_preserving_permutations_tested':tested,'compatible_nonidentity':0})
        print('exhaustive',n,tested,flush=True)
    out={'status':'PASS','prime_cases':len(pr),'prime_moment_records':pr,'block_count_cases':blocktests,'exact_permutation_sanity':ex,'elapsed':time.monotonic()-st,'scope':'Finite algebraic/formulation sanity checks only; all-order proof uses Burnside--Schur and induction.'}
    (D/'SANITY_CHECK.json').write_text(json.dumps(out,indent=2));print({'status':'PASS','primes':len(pr),'block_count_cases':blocktests,'elapsed':out['elapsed']})

if __name__=='__main__':main()
