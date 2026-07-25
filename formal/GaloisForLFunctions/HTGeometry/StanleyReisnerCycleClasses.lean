import GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation

/-!
# Cycle-family Hochster classes: nonzero `Tor₂` and `Tor₃` of the square and pentagon

Concrete nonzero Koszul-homology classes of Stanley–Reisner rings realizing the Hochster strand
equivalence `Tor_i ≅ H̃^{|σ|-i-1}` for cycle graphs: the square `C₄` (a `Tor₂ = H̃¹` class) and the
pentagon `C₅` (a `Tor₃ = H̃¹` class).  Each is a Koszul cycle that is not a boundary in every
characteristic, certified by an edge-sum detector functional on the vertex Koszul complex built in
`StanleyReisnerVertexRelation`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {R α : Type*} [CommRing R] [DecidableEq α] [Fintype α]

/-- The `4`-cycle (`C₄`) second Koszul cycle: `c_{ab} = x_c x_d`, `c_{cd} = x_a x_b`.  On the square
`a–b–c–d–a` (diagonals `{a,c}`, `{b,d}` absent) this is a degree-2 syzygy at multidegree
`{a,b,c,d}`. -/
def c4Cycle (R : Type*) [CommRing R] (facets : Finset (Finset α)) (a b c d : α) :
    α → α → stanleyReisnerRing R facets := fun i j =>
  if i = a ∧ j = b then srVertexX R facets c * srVertexX R facets d
  else if i = c ∧ j = d then srVertexX R facets a * srVertexX R facets b
  else 0

/-- **The two-edge `C₄` syzygy is a second Koszul cycle.**  The symmetric two-edge sum is annihilated
by the second differential: every boundary term carries an absent diagonal product `x_a x_c` or
`x_b x_d`, which vanishes.  It is a `d₂`-cycle at multidegree `{a,b,c,d}` in every characteristic.
Its class in `Tor₂` is nonzero only away from characteristic two — in characteristic two the two-edge
sum `(1,0,1,0)` lies in `im d₃`; the unconditional `Tor₂` representative is the single edge
`srSquareEdgeCycle` (whose class survives in every characteristic). -/
theorem srKoszulBoundary_c4Cycle (facets : Finset (Finset α)) {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    srKoszulBoundary facets (c4Cycle R facets a b c d) = 0 := by
  have hac0 : srVertexX R facets a * srVertexX R facets c = 0 :=
    srVertexX_mul_eq_zero_of_not_isFace facets hac hac_nf
  have hbd0 : srVertexX R facets b * srVertexX R facets d = 0 :=
    srVertexX_mul_eq_zero_of_not_isFace facets hbd hbd_nf
  have p1 : srVertexX R facets c * srVertexX R facets d * srVertexX R facets b = 0 := by
    rw [mul_assoc, mul_comm (srVertexX R facets d) (srVertexX R facets b), hbd0, mul_zero]
  have p2 : srVertexX R facets a * srVertexX R facets b * srVertexX R facets d = 0 := by
    rw [mul_assoc, hbd0, mul_zero]
  have p3 : srVertexX R facets c * srVertexX R facets d * srVertexX R facets a = 0 := by
    rw [mul_comm (srVertexX R facets c) (srVertexX R facets d), mul_assoc,
      mul_comm (srVertexX R facets c) (srVertexX R facets a), hac0, mul_zero]
  have p4 : srVertexX R facets a * srVertexX R facets b * srVertexX R facets c = 0 := by
    rw [mul_comm (srVertexX R facets a) (srVertexX R facets b), mul_assoc, hac0, mul_zero]
  have p3n : -(srVertexX R facets c * srVertexX R facets d) * srVertexX R facets a = 0 := by
    linear_combination -p3
  have p4n : -(srVertexX R facets a * srVertexX R facets b) * srVertexX R facets c = 0 := by
    linear_combination -p4
  funext i
  simp only [Pi.zero_apply, srKoszulBoundary]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [c4Cycle]
  split_ifs with h1 h2 h3 h4 h5 h6 <;>
    simp_all [sub_mul, sub_zero, zero_sub, zero_mul]

/-- The single-edge second Koszul cycle: `c_{ab} = x_c x_d`, all other entries zero.  On the square
`C₄` (diagonals `{a,c}`, `{b,d}` absent) this is the **unconditional** `Tor₂` representative. -/
def srSquareEdgeCycle (R : Type*) [CommRing R] (facets : Finset (Finset α)) (a b c d : α) :
    α → α → stanleyReisnerRing R facets := fun i j =>
  if i = a ∧ j = b then srVertexX R facets c * srVertexX R facets d else 0

/-- **Single-edge `C₄` syzygy is a second Koszul cycle.**  The one-entry syzygy `c_{ab} = x_c x_d` is
annihilated by the second differential: the two boundary terms carry the absent diagonals `x_b x_d`
(at vertex `a`) and `x_a x_c` (at vertex `b`), both zero.  Unlike the two-edge sum, its `Tor₂` class
is nonzero in every characteristic — the alternating detector `+{cd}∘c_{ab} − {ad}∘c_{bc} +
{ab}∘c_{cd} − {bc}∘c_{da}` evaluates it to `1`, forcing `0 = 1` in any field if it were a boundary. -/
theorem srKoszulBoundary_srSquareEdgeCycle (facets : Finset (Finset α)) {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbd : b ≠ d)
    (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    srKoszulBoundary facets (srSquareEdgeCycle R facets a b c d) = 0 := by
  have hac0 : srVertexX R facets a * srVertexX R facets c = 0 :=
    srVertexX_mul_eq_zero_of_not_isFace facets hac hac_nf
  have hbd0 : srVertexX R facets b * srVertexX R facets d = 0 :=
    srVertexX_mul_eq_zero_of_not_isFace facets hbd hbd_nf
  have p1 : srVertexX R facets c * srVertexX R facets d * srVertexX R facets b = 0 := by
    rw [mul_assoc, mul_comm (srVertexX R facets d) (srVertexX R facets b), hbd0, mul_zero]
  have p3 : srVertexX R facets c * srVertexX R facets d * srVertexX R facets a = 0 := by
    rw [mul_comm (srVertexX R facets c) (srVertexX R facets d), mul_assoc,
      mul_comm (srVertexX R facets c) (srVertexX R facets a), hac0, mul_zero]
  have p3n : -(srVertexX R facets c * srVertexX R facets d) * srVertexX R facets a = 0 := by
    linear_combination -p3
  funext i
  simp only [Pi.zero_apply, srKoszulBoundary]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  by_cases hij : i = a ∧ j = b
  · have hji : ¬ (j = a ∧ i = b) := fun h => hab (hij.1.symm.trans h.2)
    simp only [srSquareEdgeCycle, if_pos hij, if_neg hji, sub_zero]
    rw [hij.2]; exact p1
  · by_cases hji : j = a ∧ i = b
    · simp only [srSquareEdgeCycle, if_neg hij, if_pos hji, zero_sub]
      rw [hji.1]; exact p3n
    · simp only [srSquareEdgeCycle, if_neg hij, if_neg hji, sub_zero, zero_mul]

/-- **Pair detector of a third-differential entry.**  Reading the `x_u x_v` coefficient of
`d₃(b)_{ij} = ∑_k b_{ijk} x_k` collapses (product rule) to the two degree-one detectors of the
`u`- and `v`-slots: `srH0Det_v(b_{iju}) + srH0Det_u(b_{ijv})`. -/
theorem srPairDetector_srKoszulBoundary3 (facets : Finset (Finset α)) {u v : α} (huv : u ≠ v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v})
    (hu : IsFaceOf (↑facets : Set (Finset α)) {u}) (hv : IsFaceOf (↑facets : Set (Finset α)) {v})
    (b : α → α → α → stanleyReisnerRing R facets) (i j : α) :
    srPairDetector R facets u v huv hf (srKoszulBoundary3 facets b i j)
      = srH0Detector R facets v hv (b i j u) + srH0Detector R facets u hu (b i j v) := by
  rw [srKoszulBoundary3, map_sum,
    Finset.sum_congr rfl (fun k _ => srPairDetector_mul_srVertexX facets huv hf hu hv (b i j k)),
    Finset.sum_congr rfl (fun k _ => show
      (if k = u then srH0Detector R facets v hv (b i j k)
        else if k = v then srH0Detector R facets u hu (b i j k) else 0)
      = (if k = u then srH0Detector R facets v hv (b i j k) else 0)
        + (if k = v then srH0Detector R facets u hu (b i j k) else 0) from by
      by_cases hku : k = u
      · subst hku; simp [huv]
      · by_cases hkv : k = v
        · subst hkv; simp [hku]
        · simp [hku, hkv]),
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ u, Finset.sum_ite_eq' Finset.univ v]
  simp

/-- **The single-edge `C₄` cycle is a nonzero `Tor₂` class (unconditional non-boundary).**  On the
square `C₄` (all four singletons and edges `{a,b},{b,c},{c,d},{a,d}` faces; diagonals absent), the
single-edge syzygy `srSquareEdgeCycle` is not a third-Koszul boundary of any alternating 3-tensor, in
every characteristic.  The alternating detector `Φ = +{cd}∘t_{ab} − {ad}∘t_{bc} + {ab}∘t_{cd} −
{bc}∘t_{da}` evaluates the cycle to `1` but every `d₃`-boundary to `0`: the eight degree-one detector
terms pair off by the cyclic (even-permutation) invariance of the alternating coefficient (`b_{bca} =
b_{abc}`, …), so `Φ(d₃ b) = 0`.  A boundary would force `1 = 0`. -/
theorem srSquareEdgeCycle_not_koszulBoundary3 [Nontrivial R] (facets : Finset (Finset α))
    {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hcd : c ≠ d)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d}) :
    ¬ ∃ b3 : α → α → α → stanleyReisnerRing R facets,
        IsAlternating3 b3 ∧ srKoszulBoundary3 facets b3 = srSquareEdgeCycle R facets a b c d := by
  rintro ⟨b3, hb3, hEq⟩
  set Φ : (α → α → stanleyReisnerRing R facets) → R := fun t =>
    srPairDetector R facets c d hcd hcd_f (t a b)
      - srPairDetector R facets a d had had_f (t b c)
      + srPairDetector R facets a b hab hab_f (t c d)
      - srPairDetector R facets b c hbc hbc_f (t d a) with hΦ
  have hone : Φ (srSquareEdgeCycle R facets a b c d) = 1 := by
    have t1 : srSquareEdgeCycle R facets a b c d a b
        = srVertexX R facets c * srVertexX R facets d := if_pos ⟨rfl, rfl⟩
    have t2 : srSquareEdgeCycle R facets a b c d b c = 0 := if_neg (fun h => hab h.1.symm)
    have t3 : srSquareEdgeCycle R facets a b c d c d = 0 := if_neg (fun h => hac h.1.symm)
    have t4 : srSquareEdgeCycle R facets a b c d d a = 0 := if_neg (fun h => had h.1.symm)
    simp only [hΦ, t1, t2, t3, t4, map_zero, sub_zero, add_zero]
    rw [srPairDetector_srVertexX_mul facets hcd hcd_f]
  have hzero : Φ (srKoszulBoundary3 facets b3) = 0 := by
    simp only [hΦ]
    rw [srPairDetector_srKoszulBoundary3 facets hcd hcd_f hc hd b3 a b,
        srPairDetector_srKoszulBoundary3 facets had had_f ha hd b3 b c,
        srPairDetector_srKoszulBoundary3 facets hab hab_f ha hb b3 c d,
        srPairDetector_srKoszulBoundary3 facets hbc hbc_f hb hc b3 d a]
    have e1 : b3 b c a = b3 a b c := by rw [hb3.antisym23 b c a, hb3.antisym12 b a c, neg_neg]
    have e2 : b3 d a b = b3 a b d := by rw [hb3.antisym12 d a b, hb3.antisym23 a d b, neg_neg]
    have e3 : b3 c d b = b3 b c d := by rw [hb3.antisym23 c d b, hb3.antisym12 c b d, neg_neg]
    have e4 : b3 d a c = b3 c d a := by rw [hb3.antisym23 d a c, hb3.antisym12 d c a, neg_neg]
    rw [e1, e2, e3, e4]
    abel
  rw [hEq] at hzero
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- **Nonzero second Koszul homology of `C₄` (`Tor₂ = H̃¹`).**  On the square `C₄` — singletons and
edges `{a,b},{b,c},{c,d},{a,d}` faces, diagonals `{a,c},{b,d}` absent — the single-edge syzygy
`srSquareEdgeCycle` is simultaneously a second Koszul cycle (`d₂` kills it) and not a third Koszul
boundary (`∉ im d₃`), in every characteristic.  It therefore represents a nonzero class in
`Tor_{2,{a,b,c,d}} = H̃¹(C₄)` — the first genuinely second-degree Hochster homology, unconditional. -/
theorem srSquareEdge_secondKoszulHomology_nonzero [Nontrivial R] (facets : Finset (Finset α))
    {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d})
    (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    srKoszulBoundary facets (srSquareEdgeCycle R facets a b c d) = 0
      ∧ ¬ ∃ b3 : α → α → α → stanleyReisnerRing R facets,
        IsAlternating3 b3 ∧ srKoszulBoundary3 facets b3 = srSquareEdgeCycle R facets a b c d :=
  ⟨srKoszulBoundary_srSquareEdgeCycle facets hab hac hbd hac_nf hbd_nf,
    srSquareEdgeCycle_not_koszulBoundary3 facets hab hac had hbc hcd
      ha hb hc hd hab_f hbc_f hcd_f had_f⟩

/-- The single-entry pentagon (`C₅`) third Koszul cycle: `c_{abc} = x_d x_e`, all other entries zero.
On the `5`-cycle `a–b–c–d–e–a` (only the pentagon edges present) this is a `Tor₃` representative at
multidegree `{a,b,c,d,e}`. -/
def srPentTripleCycle (R : Type*) [CommRing R] (facets : Finset (Finset α)) (a b c d e : α) :
    α → α → α → stanleyReisnerRing R facets := fun i j k =>
  if i = a ∧ j = b ∧ k = c then srVertexX R facets d * srVertexX R facets e else 0

/-- **Single-entry `C₅` syzygy is a third Koszul cycle.**  The one-entry 3-tensor `c_{abc} = x_d x_e`
is annihilated by the third differential: its only boundary term `x_c x_d x_e` (at the `ab` slot)
carries the absent diagonal `x_c x_e` (`{c,e}` a non-edge of the pentagon), which vanishes.  Modulo
`im d₄` this represents `Tor_{3,{a,b,c,d,e}} = H̃¹(C₅)`. -/
theorem srKoszulBoundary3_srPentTripleCycle (facets : Finset (Finset α)) {a b c d e : α}
    (hce : c ≠ e) (hce_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {c, e}) :
    srKoszulBoundary3 facets (srPentTripleCycle R facets a b c d e) = 0 := by
  have hce0 : srVertexX R facets c * srVertexX R facets e = 0 :=
    srVertexX_mul_eq_zero_of_not_isFace facets hce hce_nf
  funext i j
  simp only [Pi.zero_apply, srKoszulBoundary3, srPentTripleCycle]
  by_cases hij : i = a ∧ j = b
  · rw [Finset.sum_eq_single c
        (fun k _ hkc => by rw [if_neg (fun h => hkc h.2.2), zero_mul])
        (fun h => absurd (Finset.mem_univ c) h),
      if_pos ⟨hij.1, hij.2, rfl⟩, mul_assoc,
      mul_comm (srVertexX R facets e) (srVertexX R facets c), hce0, mul_zero]
  · refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [if_neg (fun h => hij ⟨h.1, h.2.1⟩), zero_mul]

/-- **Pair detector of a fourth-differential entry.**  Reading the `x_u x_v` coefficient of
`d₄(b)_{ijk} = ∑_l b_{ijkl} x_l` collapses to `srH0Det_v(b_{ijku}) + srH0Det_u(b_{ijkv})`. -/
theorem srPairDetector_srKoszulBoundary4 (facets : Finset (Finset α)) {u v : α} (huv : u ≠ v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v})
    (hu : IsFaceOf (↑facets : Set (Finset α)) {u}) (hv : IsFaceOf (↑facets : Set (Finset α)) {v})
    (b : α → α → α → α → stanleyReisnerRing R facets) (i j k : α) :
    srPairDetector R facets u v huv hf (srKoszulBoundary4 facets b i j k)
      = srH0Detector R facets v hv (b i j k u) + srH0Detector R facets u hu (b i j k v) := by
  rw [srKoszulBoundary4, map_sum,
    Finset.sum_congr rfl (fun l _ => srPairDetector_mul_srVertexX facets huv hf hu hv (b i j k l)),
    Finset.sum_congr rfl (fun l _ => show
      (if l = u then srH0Detector R facets v hv (b i j k l)
        else if l = v then srH0Detector R facets u hu (b i j k l) else 0)
      = (if l = u then srH0Detector R facets v hv (b i j k l) else 0)
        + (if l = v then srH0Detector R facets u hu (b i j k l) else 0) from by
      by_cases hlu : l = u
      · subst hlu; simp [huv]
      · by_cases hlv : l = v
        · subst hlv; simp [hlu]
        · simp [hlu, hlv]),
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ u, Finset.sum_ite_eq' Finset.univ v]
  simp

/-- **The single-entry `C₅` cycle is a nonzero `Tor₃` class (unconditional non-boundary).**  On the
pentagon `C₅` (singletons and edges `{a,b},{b,c},{c,d},{d,e},{e,a}` faces; diagonals absent), the
single-entry syzygy `srPentTripleCycle` is not a fourth-Koszul boundary of any alternating 4-tensor,
in every characteristic.  The all-ones edge detector `Φ = ∑ {opposite pair}∘t_{triple}` evaluates the
cycle to `1` but every `d₄`-boundary to `0`: the ten degree-one detector terms pair off by the
odd-permutation antisymmetry of the alternating coefficient (`b_{cdeb} = −b_{bcde}`, …).  A boundary
would force `1 = 0`. -/
theorem srPentTripleCycle_not_koszulBoundary4 [Nontrivial R] (facets : Finset (Finset α))
    {a b c d e : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hea : e ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a}) :
    ¬ ∃ b4 : α → α → α → α → stanleyReisnerRing R facets,
        IsAlternating4 b4 ∧ srKoszulBoundary4 facets b4 = srPentTripleCycle R facets a b c d e := by
  rintro ⟨b4, hb4, hEq⟩
  set Φ : (α → α → α → stanleyReisnerRing R facets) → R := fun t =>
    srPairDetector R facets a b hab hab_f (t c d e)
      + srPairDetector R facets b c hbc hbc_f (t a d e)
      + srPairDetector R facets c d hcd hcd_f (t a b e)
      + srPairDetector R facets d e hde hde_f (t a b c)
      + srPairDetector R facets e a hea hea_f (t b c d) with hΦ
  have hone : Φ (srPentTripleCycle R facets a b c d e) = 1 := by
    have t0 : srPentTripleCycle R facets a b c d e c d e = 0 := if_neg (fun h => hac h.1.symm)
    have t1 : srPentTripleCycle R facets a b c d e a d e = 0 := if_neg (fun h => hbd h.2.1.symm)
    have t2 : srPentTripleCycle R facets a b c d e a b e = 0 := if_neg (fun h => hce h.2.2.symm)
    have t3 : srPentTripleCycle R facets a b c d e a b c
        = srVertexX R facets d * srVertexX R facets e := if_pos ⟨rfl, rfl, rfl⟩
    have t4 : srPentTripleCycle R facets a b c d e b c d = 0 := if_neg (fun h => hab h.1.symm)
    simp only [hΦ, t0, t1, t2, t3, t4, map_zero, add_zero, zero_add]
    rw [srPairDetector_srVertexX_mul facets hde hde_f]
  have hzero : Φ (srKoszulBoundary4 facets b4) = 0 := by
    simp only [hΦ]
    rw [srPairDetector_srKoszulBoundary4 facets hab hab_f ha hb b4 c d e,
        srPairDetector_srKoszulBoundary4 facets hbc hbc_f hb hc b4 a d e,
        srPairDetector_srKoszulBoundary4 facets hcd hcd_f hc hd b4 a b e,
        srPairDetector_srKoszulBoundary4 facets hde hde_f hd he b4 a b c,
        srPairDetector_srKoszulBoundary4 facets hea hea_f he ha b4 b c d]
    have r1 : b4 c d e b = -b4 b c d e := by
      rw [hb4.antisym34 c d e b, hb4.antisym23 c d b e, hb4.antisym12 c b d e]; ring
    have r2 : b4 a d e c = -b4 c d e a := by
      rw [hb4.antisym12 a d e c, hb4.antisym23 d a e c, hb4.antisym34 d e a c,
        hb4.antisym23 d e c a, hb4.antisym12 d c e a]; ring
    have r3 : b4 a b e d = -b4 a d e b := by
      rw [hb4.antisym23 a b e d, hb4.antisym34 a e b d, hb4.antisym23 a e d b]; ring
    have r4 : b4 a b c e = -b4 a b e c := by rw [hb4.antisym34 a b c e]
    have r5 : b4 b c d a = -b4 a b c d := by
      rw [hb4.antisym34 b c d a, hb4.antisym23 b c a d, hb4.antisym12 b a c d]; ring
    rw [r1, r2, r3, r4, r5]
    simp only [map_neg]
    abel
  rw [hEq] at hzero
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- **Nonzero third Koszul homology of `C₅` (`Tor₃ = H̃¹`).**  On the pentagon `C₅` — singletons and
edges `{a,b},{b,c},{c,d},{d,e},{e,a}` faces, diagonal `{c,e}` absent — the single-entry syzygy
`srPentTripleCycle` is simultaneously a third Koszul cycle (`d₃` kills it) and not a fourth Koszul
boundary (`∉ im d₄`), in every characteristic.  It therefore represents a nonzero class in
`Tor_{3,{a,b,c,d,e}} = H̃¹(C₅)` — the first third-degree Hochster homology, unconditional. -/
theorem srPentTriple_thirdKoszulHomology_nonzero [Nontrivial R] (facets : Finset (Finset α))
    {a b c d e : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hea : e ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a})
    (hce_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {c, e}) :
    srKoszulBoundary3 facets (srPentTripleCycle R facets a b c d e) = 0
      ∧ ¬ ∃ b4 : α → α → α → α → stanleyReisnerRing R facets,
        IsAlternating4 b4 ∧ srKoszulBoundary4 facets b4 = srPentTripleCycle R facets a b c d e :=
  ⟨srKoszulBoundary3_srPentTripleCycle facets hce hce_nf,
    srPentTripleCycle_not_koszulBoundary4 facets hab hbc hcd hde hea hac hbd hce
      ha hb hc hd he hab_f hbc_f hcd_f hde_f hea_f⟩

/-- **Pair detector of a fifth-differential entry.**  Reading the `x_u x_v` coefficient of
`d₅(b)_{ijkl} = ∑_m b_{ijklm} x_m` collapses to `srH0Det_v(b_{ijklu}) + srH0Det_u(b_{ijklv})`. -/
theorem srPairDetector_srKoszulBoundary5 (facets : Finset (Finset α)) {u v : α} (huv : u ≠ v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v})
    (hu : IsFaceOf (↑facets : Set (Finset α)) {u}) (hv : IsFaceOf (↑facets : Set (Finset α)) {v})
    (b : α → α → α → α → α → stanleyReisnerRing R facets) (i j k l : α) :
    srPairDetector R facets u v huv hf (srKoszulBoundary5 facets b i j k l)
      = srH0Detector R facets v hv (b i j k l u) + srH0Detector R facets u hu (b i j k l v) := by
  rw [srKoszulBoundary5, map_sum,
    Finset.sum_congr rfl (fun m _ => srPairDetector_mul_srVertexX facets huv hf hu hv (b i j k l m)),
    Finset.sum_congr rfl (fun m _ => show
      (if m = u then srH0Detector R facets v hv (b i j k l m)
        else if m = v then srH0Detector R facets u hu (b i j k l m) else 0)
      = (if m = u then srH0Detector R facets v hv (b i j k l m) else 0)
        + (if m = v then srH0Detector R facets u hu (b i j k l m) else 0) from by
      by_cases hmu : m = u
      · subst hmu; simp [huv]
      · by_cases hmv : m = v
        · subst hmv; simp [hmu]
        · simp [hmu, hmv]),
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ u, Finset.sum_ite_eq' Finset.univ v]
  simp

/-- The single-entry hexagon (`C₆`) fourth Koszul cycle: `c_{abcd} = x_e x_f`, all other entries zero.
On the `6`-cycle `a–b–c–d–e–f–a` (only the hexagon edges present) this is a `Tor₄` representative at
multidegree `{a,b,c,d,e,f}`. -/
def srHexTupleCycle (R : Type*) [CommRing R] (facets : Finset (Finset α)) (a b c d e f : α) :
    α → α → α → α → stanleyReisnerRing R facets := fun i j k l =>
  if i = a ∧ j = b ∧ k = c ∧ l = d then srVertexX R facets e * srVertexX R facets f else 0

/-- **Single-entry `C₆` syzygy is a fourth Koszul cycle.**  The one-entry 4-tensor `c_{abcd} = x_e x_f`
is annihilated by the fourth differential: its only boundary term `x_d x_e x_f` (at the `abc` slot)
carries the absent diagonal `x_d x_f` (`{d,f}` a non-edge of the hexagon), which vanishes.  Modulo
`im d₅` this represents `Tor_{4,{a,b,c,d,e,f}} = H̃¹(C₆)`. -/
theorem srKoszulBoundary4_srHexTupleCycle (facets : Finset (Finset α)) {a b c d e f : α}
    (hdf : d ≠ f) (hdf_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {d, f}) :
    srKoszulBoundary4 facets (srHexTupleCycle R facets a b c d e f) = 0 := by
  have hdf0 : srVertexX R facets d * srVertexX R facets f = 0 :=
    srVertexX_mul_eq_zero_of_not_isFace facets hdf hdf_nf
  funext i j k
  simp only [Pi.zero_apply, srKoszulBoundary4, srHexTupleCycle]
  by_cases hijk : i = a ∧ j = b ∧ k = c
  · rw [Finset.sum_eq_single d
        (fun l _ hld => by rw [if_neg (fun h => hld h.2.2.2), zero_mul])
        (fun h => absurd (Finset.mem_univ d) h),
      if_pos ⟨hijk.1, hijk.2.1, hijk.2.2, rfl⟩, mul_assoc,
      mul_comm (srVertexX R facets f) (srVertexX R facets d), hdf0, mul_zero]
  · refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [if_neg (fun h => hijk ⟨h.1, h.2.1, h.2.2.1⟩), zero_mul]

/-- **The single-entry `C₆` cycle is a nonzero `Tor₄` class (unconditional non-boundary).**  On the
hexagon `C₆` (singletons and edges `{a,b},…,{f,a}` faces; diagonals absent), `srHexTupleCycle` is not a
fifth-Koszul boundary of any alternating 5-tensor, in every characteristic.  The edge detector
`Φ = +ab+bc+cd+de+ef−fa` (even cycle: one sign flip, from the two 5-cycle pairings) evaluates the cycle
to `1` but every `d₅`-boundary to `0`: the twelve degree-one detector terms pair off by the
permutation antisymmetry of the alternating coefficient (`b_{cdefb}=b_{bcdef}`, `b_{adefc}=−b_{cdefa}`,
…).  A boundary would force `1 = 0`.  (Numerically pre-certified over `GF(2,3,5,7)`.) -/
theorem srHexTupleCycle_not_koszulBoundary5 [Nontrivial R] (facets : Finset (Finset α))
    {a b c d e f : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f)
    (hfa : f ≠ a) (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) (hdf : d ≠ f)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) (hf : IsFaceOf (↑facets : Set (Finset α)) {f})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a}) :
    ¬ ∃ b5 : α → α → α → α → α → stanleyReisnerRing R facets,
        IsAlternating5 b5 ∧ srKoszulBoundary5 facets b5 = srHexTupleCycle R facets a b c d e f := by
  rintro ⟨b5, hb5, hEq⟩
  set Φ : (α → α → α → α → stanleyReisnerRing R facets) → R := fun t =>
    srPairDetector R facets a b hab hab_f (t c d e f)
      + srPairDetector R facets b c hbc hbc_f (t a d e f)
      + srPairDetector R facets c d hcd hcd_f (t a b e f)
      + srPairDetector R facets d e hde hde_f (t a b c f)
      + srPairDetector R facets e f hef hef_f (t a b c d)
      - srPairDetector R facets f a hfa hfa_f (t b c d e) with hΦ
  have hone : Φ (srHexTupleCycle R facets a b c d e f) = 1 := by
    have t0 : srHexTupleCycle R facets a b c d e f c d e f = 0 := if_neg (fun h => hac h.1.symm)
    have t1 : srHexTupleCycle R facets a b c d e f a d e f = 0 := if_neg (fun h => hbd h.2.1.symm)
    have t2 : srHexTupleCycle R facets a b c d e f a b e f = 0 := if_neg (fun h => hce h.2.2.1.symm)
    have t3 : srHexTupleCycle R facets a b c d e f a b c f = 0 := if_neg (fun h => hdf h.2.2.2.symm)
    have t4 : srHexTupleCycle R facets a b c d e f a b c d
        = srVertexX R facets e * srVertexX R facets f := if_pos ⟨rfl, rfl, rfl, rfl⟩
    have t5 : srHexTupleCycle R facets a b c d e f b c d e = 0 := if_neg (fun h => hab h.1.symm)
    simp only [hΦ, t0, t1, t2, t3, t4, t5, map_zero, add_zero, zero_add, sub_zero]
    rw [srPairDetector_srVertexX_mul facets hef hef_f]
  have hzero : Φ (srKoszulBoundary5 facets b5) = 0 := by
    simp only [hΦ]
    rw [srPairDetector_srKoszulBoundary5 facets hab hab_f ha hb b5 c d e f,
        srPairDetector_srKoszulBoundary5 facets hbc hbc_f hb hc b5 a d e f,
        srPairDetector_srKoszulBoundary5 facets hcd hcd_f hc hd b5 a b e f,
        srPairDetector_srKoszulBoundary5 facets hde hde_f hd he b5 a b c f,
        srPairDetector_srKoszulBoundary5 facets hef hef_f he hf b5 a b c d,
        srPairDetector_srKoszulBoundary5 facets hfa hfa_f hf ha b5 b c d e]
    have ra : b5 c d e f b = b5 b c d e f := by
      rw [hb5.antisym45 c d e f b, hb5.antisym34 c d e b f, hb5.antisym23 c d b e f,
        hb5.antisym12 c b d e f]; ring
    have rb : b5 a d e f c = -b5 c d e f a := by
      rw [hb5.antisym45 a d e f c, hb5.antisym34 a d e c f, hb5.antisym23 a d c e f,
        hb5.antisym12 a c d e f, hb5.antisym23 c a d e f, hb5.antisym34 c d a e f,
        hb5.antisym45 c d e a f]; ring
    have rc : b5 a b e f d = -b5 a d e f b := by
      rw [hb5.antisym45 a b e f d, hb5.antisym34 a b e d f, hb5.antisym23 a b d e f,
        hb5.antisym34 a d b e f, hb5.antisym45 a d e b f]; ring
    have rd : b5 a b c f e = -b5 a b e f c := by
      rw [hb5.antisym45 a b c f e, hb5.antisym34 a b c e f, hb5.antisym45 a b e c f]; ring
    have re : b5 a b c d f = -b5 a b c f d := by rw [hb5.antisym45 a b c d f]
    have rf : b5 b c d e a = b5 a b c d e := by
      rw [hb5.antisym45 b c d e a, hb5.antisym34 b c d a e, hb5.antisym23 b c a d e,
        hb5.antisym12 b a c d e]; ring
    rw [ra, rb, rc, rd, re, rf]
    simp only [map_neg]
    abel
  rw [hEq] at hzero
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- **Nonzero fourth Koszul homology of `C₆` (`Tor₄ = H̃¹`).**  On the hexagon `C₆` the single-entry
syzygy `srHexTupleCycle` is simultaneously a fourth Koszul cycle and not a fifth Koszul boundary, in
every characteristic — a nonzero class in `Tor_{4,{a,b,c,d,e,f}} = H̃¹(C₆)`, the first fourth-degree
Hochster homology, unconditional. -/
theorem srHexTuple_fourthKoszulHomology_nonzero [Nontrivial R] (facets : Finset (Finset α))
    {a b c d e f : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f)
    (hfa : f ≠ a) (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) (hdf : d ≠ f)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) (hf : IsFaceOf (↑facets : Set (Finset α)) {f})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a})
    (hdf_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {d, f}) :
    srKoszulBoundary4 facets (srHexTupleCycle R facets a b c d e f) = 0
      ∧ ¬ ∃ b5 : α → α → α → α → α → stanleyReisnerRing R facets,
        IsAlternating5 b5 ∧ srKoszulBoundary5 facets b5 = srHexTupleCycle R facets a b c d e f :=
  ⟨srKoszulBoundary4_srHexTupleCycle facets hdf hdf_nf,
    srHexTupleCycle_not_koszulBoundary5 facets hab hbc hcd hde hef hfa hac hbd hce hdf
      ha hb hc hd he hf hab_f hbc_f hcd_f hde_f hef_f hfa_f⟩

end

end GaloisForLFunctions.HTGeometry
