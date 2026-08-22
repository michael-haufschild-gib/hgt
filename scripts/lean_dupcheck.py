import re,sys,os,collections
ROOT="GaloisForLFunctions"
DECL=re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*(theorem|lemma|def|structure|class|abbrev|inductive|instance)\s+([\w'.«»]+)")
NS=re.compile(r"^namespace\s+([\w'.]+)")
END=re.compile(r"^end\s+([\w'.]+)")
def decls(path):
    out=[]; stack=[]
    for line in open(path,encoding='utf-8',errors='replace'):
        m=NS.match(line)
        if m: stack.append(m.group(1)); continue
        m=END.match(line)
        if m and stack and stack[-1]==m.group(1): stack.pop(); continue
        m=DECL.match(line)
        if m: out.append(".".join(stack+[m.group(2)]))
    return out
targets=sys.argv[1:]
tset=set(os.path.abspath(t) for t in targets)
mine=collections.defaultdict(list)
for t in targets: 
    for d in decls(t): mine[d].append(t)
allfiles=[]
for dp,_,fns in os.walk(ROOT):
    for fn in fns:
        if fn.endswith(".lean"):
            p=os.path.join(dp,fn)
            if os.path.abspath(p) not in tset: allfiles.append(p)
hits=collections.defaultdict(list)
for p in allfiles:
    for d in decls(p):
        if d in mine: hits[d].append(p)
bad=False
for d,ps in sorted(hits.items()):
    bad=True
    print("COLLISION",d,"->",ps[:3])
for d,ts in mine.items():
    if len(ts)>1: bad=True; print("SELF-DUP",d,ts)
print("TOTAL new decls:",len(mine),"| collisions:",len(hits))
