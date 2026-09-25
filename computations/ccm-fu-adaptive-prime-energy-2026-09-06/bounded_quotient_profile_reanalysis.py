"""Read saved unit channels; never regenerate arithmetic data."""
import csv
import hashlib
import json
import math
from pathlib import Path

folder = Path(__file__).resolve().parent
source = folder / "first-prime-unit-clock.csv"
rows = list(csv.DictReader(source.read_text().splitlines()))
assert [int(r["n"]) for r in rows] == list(range(1025))
profiles = []
prefixes = []
partial = 0.0
for r in rows:
    n = int(r["n"])
    if n == 0:
        continue
    partial += float(r["defect"])
    unit = float(r["unit_channel"])
    profiles.append({"n": n, "normalized_unit": unit / math.sqrt(n),
                     "one_eighth_margin": math.sqrt(n) / 8 - unit})
    prefixes.append({"n": n, "prefix": partial,
                     "one_eighth_margin": (n+1) / 8 - partial})
result = {
    "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "count": len(profiles),
    "candidate_channel_bound_violations": sum(r["one_eighth_margin"] < -1e-10 for r in profiles),
    "maximum_normalized_unit": max(profiles, key=lambda r: r["normalized_unit"]),
    "candidate_prefix_bound_violations": sum(r["one_eighth_margin"] < -1e-10 for r in prefixes),
    "worst_prefix_margin": min(prefixes, key=lambda r: r["one_eighth_margin"]),
    "guidance_only": True,
}
(folder / "bounded-quotient-profile-reanalysis.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
