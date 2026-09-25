exec(open('/tmp/clg_even_inner_explore.py').read().split("if __name__")[0])
T={tuple(e):F(c) for e,c in json.load(open('/tmp/clg_even_inner_unit.json'))}
L={}
for e,c in T.items():
 if c<0:
  f=tuple(min(i,4) for i in e);L[f]=L.get(f,F(0))+c
 elif all(i<=4 for i in e):L[e]=L.get(e,F(0))+c
B={}
for i in product(range(5),repeat=3):
 B[i]=sum(c*F(comb(i[0],e[0]),comb(4,e[0]))*F(comb(i[1],e[1]),comb(4,e[1]))*F(comb(i[2],e[2]),comb(4,e[2])) for e,c in L.items() if all(e[j]<=i[j] for j in range(3)))
print('Bernstein minimum',min((float(c),i) for i,c in B.items()),'negative',sum(c<0 for c in B.values()))
with open('/tmp/clg_even_inner_minorant.json','w') as f:json.dump({'L':[[list(e),str(c)] for e,c in sorted(L.items())], 'B':[[list(e),str(c)] for e,c in sorted(B.items())]},f)
