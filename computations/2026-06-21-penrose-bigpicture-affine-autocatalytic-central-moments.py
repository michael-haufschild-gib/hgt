from collections import defaultdict
from itertools import combinations_with_replacement


def moments(cloud, max_k=5):
    n = len(cloud)
    mean = sum(cloud) / n
    return tuple(sum((x - mean) ** k for x in cloud) for k in range(2, max_k + 1))


groups = defaultdict(list)
for cloud in combinations_with_replacement(range(-5, 6), 4):
    passport = (len(cloud), sum(cloud))
    groups[passport].append(cloud)

passport = (4, 0)
clouds = groups[passport]
rows = [(cloud, moments(cloud)) for cloud in clouds]
rows.sort(key=lambda row: row[1])

print("Affine passport fixed: count=4, sum=0")
print(f"number_of_clouds={len(rows)}")
print("first 10 distinct mean-zero moment towers")
seen = set()
for cloud, ms in rows:
    if ms in seen:
        continue
    seen.add(ms)
    print(f"cloud={cloud} moments2-5={ms}")
    if len(seen) == 10:
        break

same_variance = defaultdict(list)
for cloud, ms in rows:
    same_variance[ms[0]].append((cloud, ms))

print("same second moment but different higher moments")
shown = 0
for second, vals in same_variance.items():
    towers = {}
    for cloud, ms in vals:
        towers.setdefault(ms[1:], cloud)
    if len(towers) >= 2:
        print(f"second_moment={second}")
        for tail, cloud in list(towers.items())[:3]:
            print(f"  cloud={cloud} tail3-5={tail}")
        shown += 1
    if shown == 3:
        break
