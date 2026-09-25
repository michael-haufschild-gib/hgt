import json
S = json.load(open("/root/precert/li_summary.json"))
print(json.dumps({k: S[k] for k in ("n_zeros","gamma_max","min_ratio_lambda_over_asym","all_lambda_positive","all_positive_with_tail")}, indent=1))
print("hankel:", json.dumps(S["hankel"], indent=1))
print("lambda_1..6:", [(r["d"], round(r["lambda"],6)) for r in S["lambda_head"][:6]])
print("lambda_298..300:", [(r["d"], round(r["lambda"],3), round(r["ratio"],4)) for r in S["lambda_tail3"]])
# smallest relative margin over all d
import math
mins = []
for line in open("/root/precert/li_lambdas.jsonl"):
    r = json.loads(line)
    mins.append((r["lambda"]/max(r["asym"],1e-9), r["d"], r["lambda"]))
mins.sort()
print("3 smallest lambda/asym ratios:", [(round(a,4), d) for a,d,_ in mins[:3]])
