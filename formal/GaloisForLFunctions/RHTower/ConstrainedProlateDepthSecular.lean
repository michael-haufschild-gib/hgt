import GaloisForLFunctions.RHTower.ConstrainedProlateInfiniteSecular
import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteContrast

/-!
# The exact constrained ladder: every fixed depth by the flattening sandwich

On the `k`-th spectral gap `(d_k, d_{k+1})` the full constrained secular function

```text
F(μ) = Σ_{j≤k} ℓ_j²/(d_j − μ) + ℓ_{k+1}²/(d_{k+1} − μ) + Σ_{j≥k+2} ℓ_j²/(d_j − μ)
```

is squeezed pointwise between two *aggregated* two-pole models: flattening all head poles down
to `0` can only increase each head term, flattening them up to `d_k` can only decrease it,
because `1/(d_k − μ) ≤ 1/(d_j − μ) ≤ 1/(0 − μ)` for `0 ≤ d_j ≤ d_k < μ`.  Both flattened
models are literal instances of the first-gap secular theory — the scale families
`(0, d_{k+1}, d_{k+2}, …)` and `(d_k, d_{k+1}, d_{k+2}, …)` with the coordinate family
`(√(Σ_{j≤k} ℓ_j²), ℓ_{k+1}, ℓ_{k+2}, …)` — so each has a unique first-gap root with normalized
limit `S_k/(S_k + a_{k+1}²)` under the transfer hypotheses.

The exact depth-`k` root is trapped: monotonicity forces it between the two flattened roots,
the intermediate value theorem produces it once the lower flattened root clears `d_k` (which
happens eventually, since its normalized limit is positive while `d_k/d_{k+1} → 0`), and strict
monotonicity on the gap makes it unique.  The squeeze then gives the exact ladder law

```text
μ_k(λ)/d_{k+1}(λ) → S_k/(S_k + a_{k+1}²),
```

which for the Connes–Consani–Moscovici Hermite coordinates is exactly `θ_k = Q_k/Q_{k+1}`:
the complete fixed-depth constrained spectrum of the exact operator selects the Hermite
contrast ladder, at every depth, with no truncation.
-/

open Filter Set

namespace RHTower

/-- Division by a fixed positive constant is monotone. -/
private theorem div_le_div_of_le_of_pos'' {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  rw [div_le_iff₀ hc, div_mul_cancel₀ _ hc.ne']
  exact h

/-- Monotonicity of `a/·` across two negative denominators. -/
private theorem div_le_div_of_neg_of_le {a b c : ℝ} (ha : 0 ≤ a) (hb : b < 0) (hcb : c ≤ b) :
    a / b ≤ a / c := by
  have h := div_le_div_of_nonneg_left ha (neg_pos.mpr hb) (neg_le_neg hcb)
  rw [div_neg, div_neg] at h
  linarith

noncomputable section

/-- The secular tail from index `m` on. -/
def offsetSecularTail (d ℓ : ℕ → ℝ) (m : ℕ) (μ : ℝ) : ℝ :=
  ∑' j : ℕ, ℓ (j + m) ^ 2 / (d (j + m) - μ)

variable {d ℓ : ℕ → ℝ} {m : ℕ} {B : ℝ}

theorem offsetSecularTail_term_nonneg (hB : ∀ j, B ≤ d (j + m)) {μ : ℝ} (hμ : μ < B) (j : ℕ) :
    0 ≤ ℓ (j + m) ^ 2 / (d (j + m) - μ) :=
  div_nonneg (sq_nonneg _) (by linarith [hB j])

theorem summable_offsetSecularTail (hB : ∀ j, B ≤ d (j + m))
    (hsum : Summable fun j => ℓ j ^ 2) {μ : ℝ} (hμ : μ < B) :
    Summable fun j : ℕ => ℓ (j + m) ^ 2 / (d (j + m) - μ) := by
  have hsum2 : Summable fun j : ℕ => ℓ (j + m) ^ 2 := (summable_nat_add_iff m).mpr hsum
  refine Summable.of_nonneg_of_le (offsetSecularTail_term_nonneg hB hμ) (fun j => ?_)
    (hsum2.div_const (B - μ))
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith [hB j])

theorem offsetSecularTail_nonneg (hB : ∀ j, B ≤ d (j + m)) {μ : ℝ} (hμ : μ < B) :
    0 ≤ offsetSecularTail d ℓ m μ :=
  tsum_nonneg (offsetSecularTail_term_nonneg hB hμ)

theorem offsetSecularTail_mono (hB : ∀ j, B ≤ d (j + m))
    (hsum : Summable fun j => ℓ j ^ 2) {μ μ' : ℝ} (hle : μ ≤ μ') (hμ' : μ' < B) :
    offsetSecularTail d ℓ m μ ≤ offsetSecularTail d ℓ m μ' := by
  refine Summable.tsum_le_tsum (fun j => ?_)
    (summable_offsetSecularTail hB hsum (lt_of_le_of_lt hle hμ'))
    (summable_offsetSecularTail hB hsum hμ')
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [hB j]) (by linarith)

theorem offsetSecularTail_continuousOn (hB : ∀ j, B ≤ d (j + m))
    (hsum : Summable fun j => ℓ j ^ 2) {b : ℝ} (hb : b < B) :
    ContinuousOn (offsetSecularTail d ℓ m) (Set.Iic b) := by
  have hsum2 : Summable fun j : ℕ => ℓ (j + m) ^ 2 := (summable_nat_add_iff m).mpr hsum
  rw [continuousOn_iff_continuous_restrict]
  have hrestrict : (Set.Iic b).restrict (offsetSecularTail d ℓ m)
      = fun x : Set.Iic b => ∑' j : ℕ, ℓ (j + m) ^ 2 / (d (j + m) - (x : ℝ)) := rfl
  rw [hrestrict]
  refine continuous_tsum (fun j => ?_) (hsum2.div_const (B - b)) (fun j x => ?_)
  · refine continuous_const.div (continuous_const.sub continuous_subtype_val) fun x => ?_
    have hx : (x : ℝ) ≤ b := x.2
    exact ne_of_gt (by linarith [hB j])
  · have hx : (x : ℝ) ≤ b := x.2
    have hpos : 0 < d (j + m) - (x : ℝ) := by linarith [hB j]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith [hB j])

/-! ## The depth-`k` secular function -/

variable {k : ℕ}

/-- The full constrained secular function split at depth `k`: head poles `0..k`, the shoulder
pole `k+1`, and the tail from `k+2` on. -/
def depthSecular (d ℓ : ℕ → ℝ) (k : ℕ) (μ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (k + 1), ℓ j ^ 2 / (d j - μ))
    + ℓ (k + 1) ^ 2 / (d (k + 1) - μ) + offsetSecularTail d ℓ (k + 2) μ

theorem depthSecular_strictMonoOn (hk12 : d (k + 1) < d (k + 2))
    (hkfloor : ∀ j, d (k + 2) ≤ d (j + (k + 2)))
    (hhead : ∀ j, j ≤ k → d j ≤ d k)
    (hsum : Summable fun j => ℓ j ^ 2) (hℓk1 : ℓ (k + 1) ≠ 0) :
    StrictMonoOn (depthSecular d ℓ k) (Set.Ioo (d k) (d (k + 1))) := by
  intro μ hμ μ' hμ' hlt
  have hc : (0 : ℝ) < ℓ (k + 1) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hℓk1))
  have hheadsum : (∑ j ∈ Finset.range (k + 1), ℓ j ^ 2 / (d j - μ))
      ≤ ∑ j ∈ Finset.range (k + 1), ℓ j ^ 2 / (d j - μ') := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact div_le_div_of_neg_of_le (sq_nonneg _)
      (by linarith [hhead j hjk, hμ.1]) (by linarith)
  have hsh : ℓ (k + 1) ^ 2 / (d (k + 1) - μ) < ℓ (k + 1) ^ 2 / (d (k + 1) - μ') :=
    div_lt_div_of_pos_left hc (by linarith [hμ'.2]) (by linarith)
  have ht : offsetSecularTail d ℓ (k + 2) μ ≤ offsetSecularTail d ℓ (k + 2) μ' :=
    offsetSecularTail_mono hkfloor hsum hlt.le (by linarith [hμ'.2])
  unfold depthSecular
  exact add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt hheadsum hsh) ht

theorem depthSecular_continuousOn (hk12 : d (k + 1) < d (k + 2))
    (hkfloor : ∀ j, d (k + 2) ≤ d (j + (k + 2)))
    (hhead : ∀ j, j ≤ k → d j ≤ d k)
    (hsum : Summable fun j => ℓ j ^ 2) {a b : ℝ} (ha : d k < a) (hb : b < d (k + 1)) :
    ContinuousOn (depthSecular d ℓ k) (Set.Icc a b) := by
  have hheadc : ContinuousOn
      (fun μ : ℝ => ∑ j ∈ Finset.range (k + 1), ℓ j ^ 2 / (d j - μ)) (Set.Icc a b) := by
    refine continuousOn_finsetSum _ fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    apply ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id)
    intro x hx
    exact ne_of_lt (by linarith [hhead j hjk, hx.1] : d j - x < 0)
  have hshc : ContinuousOn (fun μ : ℝ => ℓ (k + 1) ^ 2 / (d (k + 1) - μ)) (Set.Icc a b) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id)
    intro x hx
    exact ne_of_gt (by linarith [hx.2] : 0 < d (k + 1) - x)
  have htc : ContinuousOn (offsetSecularTail d ℓ (k + 2)) (Set.Icc a b) :=
    (offsetSecularTail_continuousOn hkfloor hsum (lt_trans hb hk12)).mono
      Set.Icc_subset_Iic_self
  exact (hheadc.add hshc).add htc

theorem depthSecular_root_unique (hk12 : d (k + 1) < d (k + 2))
    (hkfloor : ∀ j, d (k + 2) ≤ d (j + (k + 2)))
    (hhead : ∀ j, j ≤ k → d j ≤ d k)
    (hsum : Summable fun j => ℓ j ^ 2) (hℓk1 : ℓ (k + 1) ≠ 0)
    {μ μ' : ℝ} (hμ : μ ∈ Set.Ioo (d k) (d (k + 1))) (hμ' : μ' ∈ Set.Ioo (d k) (d (k + 1)))
    (h : depthSecular d ℓ k μ = 0) (h' : depthSecular d ℓ k μ' = 0) : μ = μ' :=
  (depthSecular_strictMonoOn hk12 hkfloor hhead hsum hℓk1).injOn hμ hμ' (h.trans h'.symm)

/-! ## The flattened aggregated families -/

/-- Scale family with the whole head collapsed to one pole at `t`. -/
def flattenedScales (d : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℕ → ℝ
  | 0 => t
  | 1 => d (k + 1)
  | j + 2 => d (j + (k + 2))

/-- Coordinate family with the whole head aggregated into one mass. -/
def flattenedCoords (ℓ : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => Real.sqrt (∑ j ∈ Finset.range (k + 1), ℓ j ^ 2)
  | 1 => ℓ (k + 1)
  | j + 2 => ℓ (j + (k + 2))

theorem flattenedScales_two {t : ℝ} : flattenedScales d k t 2 = d (k + 2) := by
  show d (0 + (k + 2)) = d (k + 2)
  rw [Nat.zero_add]

theorem flattenedScales_add_two {t : ℝ} (j : ℕ) :
    flattenedScales d k t (j + 2) = d (j + (k + 2)) := rfl

theorem flattenedCoords_zero_sq :
    flattenedCoords ℓ k 0 ^ 2 = ∑ j ∈ Finset.range (k + 1), ℓ j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The flattened family's first-gap secular function in closed form. -/
theorem infiniteSecular_flattened (t μ : ℝ) :
    infiniteSecular (flattenedScales d k t) (flattenedCoords ℓ k) μ
      = (∑ j ∈ Finset.range (k + 1), ℓ j ^ 2) / (t - μ)
        + ℓ (k + 1) ^ 2 / (d (k + 1) - μ) + offsetSecularTail d ℓ (k + 2) μ := by
  show flattenedCoords ℓ k 0 ^ 2 / (t - μ) + ℓ (k + 1) ^ 2 / (d (k + 1) - μ)
      + offsetSecularTail d ℓ (k + 2) μ = _
  rw [flattenedCoords_zero_sq]

theorem summable_flattenedCoords_sq (hsum : Summable fun j => ℓ j ^ 2) :
    Summable fun j => flattenedCoords ℓ k j ^ 2 := by
  have htail : Summable fun j : ℕ => flattenedCoords ℓ k (j + 2) ^ 2 :=
    (summable_nat_add_iff (k + 2)).mpr hsum
  exact (summable_nat_add_iff 2).mp htail

/-- Aggregation is mass-preserving: the flattened coordinate family carries exactly the total
squared mass of the original one. -/
theorem tsum_flattenedCoords_sq (hsum : Summable fun j => ℓ j ^ 2) :
    (∑' j : ℕ, flattenedCoords ℓ k j ^ 2) = ∑' j : ℕ, ℓ j ^ 2 := by
  have hflat := summable_flattenedCoords_sq (k := k) hsum
  have h1 := hflat.sum_add_tsum_nat_add 2
  have h2 := hsum.sum_add_tsum_nat_add (k + 2)
  have hr2 : (∑ i ∈ Finset.range 2, flattenedCoords ℓ k i ^ 2)
      = (∑ j ∈ Finset.range (k + 1), ℓ j ^ 2) + ℓ (k + 1) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, flattenedCoords_zero_sq]
  have hrk : (∑ i ∈ Finset.range (k + 2), ℓ i ^ 2)
      = (∑ j ∈ Finset.range (k + 1), ℓ j ^ 2) + ℓ (k + 1) ^ 2 := Finset.sum_range_succ _ _
  have htaileq : (∑' i : ℕ, flattenedCoords ℓ k (i + 2) ^ 2)
      = ∑' i : ℕ, ℓ (i + (k + 2)) ^ 2 := tsum_congr fun i => rfl
  linarith [h1, h2]

/-! ## The pointwise sandwich -/

/-- Flattening the head poles down to `0` can only increase the secular function on the gap. -/
theorem depthSecular_le_flattened_zero
    (hhead : ∀ j, j ≤ k → 0 ≤ d j ∧ d j ≤ d k) {μ : ℝ} (hμ : d k < μ) :
    depthSecular d ℓ k μ
      ≤ infiniteSecular (flattenedScales d k 0) (flattenedCoords ℓ k) μ := by
  rw [infiniteSecular_flattened]
  unfold depthSecular
  have hheadle : (∑ j ∈ Finset.range (k + 1), ℓ j ^ 2 / (d j - μ))
      ≤ (∑ j ∈ Finset.range (k + 1), ℓ j ^ 2) / (0 - μ) := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact div_le_div_of_neg_of_le (sq_nonneg _)
      (by linarith [(hhead j hjk).2]) (by linarith [(hhead j hjk).1])
  linarith

/-- Flattening the head poles up to `d_k` can only decrease the secular function on the gap. -/
theorem flattened_top_le_depthSecular
    (hhead : ∀ j, j ≤ k → d j ≤ d k) {μ : ℝ} (hμ : d k < μ) :
    infiniteSecular (flattenedScales d k (d k)) (flattenedCoords ℓ k) μ
      ≤ depthSecular d ℓ k μ := by
  rw [infiniteSecular_flattened]
  unfold depthSecular
  have hheadle : (∑ j ∈ Finset.range (k + 1), ℓ j ^ 2) / (d k - μ)
      ≤ ∑ j ∈ Finset.range (k + 1), ℓ j ^ 2 / (d j - μ) := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact div_le_div_of_neg_of_le (sq_nonneg _) (by linarith)
      (by linarith [hhead j hjk])
  linarith

/-! ## The exact depth-`k` root -/

open Classical in
/-- The exact constrained eigenvalue in the `k`-th spectral gap: the unique zero of the full
secular function there (junk value `0` when no root exists). -/
def depthSecularRoot (d ℓ : ℕ → ℝ) (k : ℕ) : ℝ :=
  if h : ∃ μ ∈ Set.Ioo (d k) (d (k + 1)), depthSecular d ℓ k μ = 0 then h.choose else 0

/-- **The bracket theorem.**  Once the lower flattened root clears `d_k`, the exact depth-`k`
root exists, is trapped between the two flattened roots, and kills the secular function. -/
theorem depthSecularRoot_bracket
    (hk01 : d k < d (k + 1)) (hk12 : d (k + 1) < d (k + 2))
    (hkfloor : ∀ j, d (k + 2) ≤ d (j + (k + 2)))
    (hhead : ∀ j, j ≤ k → 0 ≤ d j ∧ d j ≤ d k)
    (hsum : Summable fun j => ℓ j ^ 2)
    (hS : flattenedCoords ℓ k 0 ≠ 0) (hℓk1 : ℓ (k + 1) ≠ 0)
    (hbr : d k < infiniteSecularRoot (flattenedScales d k 0) (flattenedCoords ℓ k)) :
    depthSecularRoot d ℓ k ∈ Set.Ioo (d k) (d (k + 1)) ∧
      depthSecular d ℓ k (depthSecularRoot d ℓ k) = 0 ∧
      infiniteSecularRoot (flattenedScales d k 0) (flattenedCoords ℓ k)
        ≤ depthSecularRoot d ℓ k ∧
      depthSecularRoot d ℓ k
        ≤ infiniteSecularRoot (flattenedScales d k (d k)) (flattenedCoords ℓ k) := by
  have hd0k : 0 ≤ d k := (hhead k le_rfl).1
  have hheadle : ∀ j, j ≤ k → d j ≤ d k := fun j hj => (hhead j hj).2
  have hsumflat : Summable fun j => flattenedCoords ℓ k j ^ 2 :=
    summable_flattenedCoords_sq hsum
  -- structure of the two flattened families
  have h12z : flattenedScales d k (0 : ℝ) 1 < flattenedScales d k 0 2 := by
    rw [flattenedScales_two]; exact hk12
  have hd2z : ∀ j, flattenedScales d k (0 : ℝ) 2 ≤ flattenedScales d k 0 (j + 2) := by
    intro j; rw [flattenedScales_two, flattenedScales_add_two]; exact hkfloor j
  have h12t : flattenedScales d k (d k) 1 < flattenedScales d k (d k) 2 := by
    rw [flattenedScales_two]; exact hk12
  have hd2t : ∀ j, flattenedScales d k (d k) 2 ≤ flattenedScales d k (d k) (j + 2) := by
    intro j; rw [flattenedScales_two, flattenedScales_add_two]; exact hkfloor j
  have h01z : flattenedScales d k (0 : ℝ) 0 < flattenedScales d k 0 1 :=
    lt_of_le_of_lt hd0k hk01
  have h01t : flattenedScales d k (d k) 0 < flattenedScales d k (d k) 1 := hk01
  -- the two flattened roots
  obtain ⟨hřmem, hř0, _⟩ := infiniteSecularRoot_spec (d := flattenedScales d k 0)
    (ℓ := flattenedCoords ℓ k) h01z h12z hd2z hsumflat hS hℓk1
  obtain ⟨hr̂mem, hr̂0, _⟩ := infiniteSecularRoot_spec (d := flattenedScales d k (d k))
    (ℓ := flattenedCoords ℓ k) h01t h12t hd2t hsumflat hS hℓk1
  set ř := infiniteSecularRoot (flattenedScales d k 0) (flattenedCoords ℓ k) with hřdef
  set r̂ := infiniteSecularRoot (flattenedScales d k (d k)) (flattenedCoords ℓ k) with hr̂def
  have hřgap : ř ∈ Set.Ioo (d k) (d (k + 1)) := ⟨hbr, hřmem.2⟩
  have hr̂gap : r̂ ∈ Set.Ioo (d k) (d (k + 1)) := ⟨hr̂mem.1, hr̂mem.2⟩
  -- sandwich values at the two flattened roots
  have hFř : depthSecular d ℓ k ř ≤ 0 := by
    have h := depthSecular_le_flattened_zero (ℓ := ℓ) hhead hbr
    rw [hř0] at h
    exact h
  have hFr̂ : 0 ≤ depthSecular d ℓ k r̂ := by
    have h := flattened_top_le_depthSecular (ℓ := ℓ) hheadle hr̂mem.1
    rw [hr̂0] at h
    exact h
  -- ordering of the flattened roots
  have hmonot : StrictMonoOn
      (infiniteSecular (flattenedScales d k (d k)) (flattenedCoords ℓ k))
      (Set.Ioo (d k) (d (k + 1))) :=
    infiniteSecular_strictMonoOn h12t hd2t hsumflat hS
  have hřr̂ : ř ≤ r̂ := by
    have h1 : infiniteSecular (flattenedScales d k (d k)) (flattenedCoords ℓ k) ř
        ≤ depthSecular d ℓ k ř := flattened_top_le_depthSecular hheadle hbr
    have h2 : infiniteSecular (flattenedScales d k (d k)) (flattenedCoords ℓ k) ř
        ≤ infiniteSecular (flattenedScales d k (d k)) (flattenedCoords ℓ k) r̂ := by
      rw [hr̂0]
      linarith
    exact (hmonot.le_iff_le hřgap hr̂gap).mp h2
  -- the exact root by the intermediate value theorem
  have hcont : ContinuousOn (depthSecular d ℓ k) (Set.Icc ř r̂) :=
    depthSecular_continuousOn hk12 hkfloor hheadle hsum hbr hr̂mem.2
  have hivt := intermediate_value_Icc hřr̂ hcont
  obtain ⟨r, hrmem, hr0⟩ := hivt ⟨hFř, hFr̂⟩
  have hrgap : r ∈ Set.Ioo (d k) (d (k + 1)) :=
    ⟨lt_of_lt_of_le hbr hrmem.1, lt_of_le_of_lt hrmem.2 hr̂mem.2⟩
  have hex : ∃ μ ∈ Set.Ioo (d k) (d (k + 1)), depthSecular d ℓ k μ = 0 := ⟨r, hrgap, hr0⟩
  rw [depthSecularRoot, dif_pos hex]
  obtain ⟨hcmem, hc0⟩ := hex.choose_spec
  have heq : hex.choose = r :=
    depthSecular_root_unique hk12 hkfloor hheadle hsum hℓk1 hcmem hrgap hc0 hr0
  refine ⟨hcmem, hc0, ?_, ?_⟩
  · rw [heq]; exact hrmem.1
  · rw [heq]; exact hrmem.2

end

/-! ## The all-depth family theorem -/

/-- **The exact ladder law.**  Under the depth-`k` transfer hypotheses, the exact constrained
root in the `k`-th spectral gap keeps the aggregated two-mode limit: the whole infinite tail
and the whole multi-pole head are invisible, and

```text
μ_k(λ)/d_{k+1}(λ) → S_k/(S_k + a_{k+1}²).
``` -/
theorem depthSecularRoot_ratio_tendsto
    {d ℓ : ℝ → ℕ → ℝ} {k : ℕ} {a : ℕ → ℝ}
    (haS : 0 < ∑ j ∈ Finset.range (k + 1), a j ^ 2) (hak1 : a (k + 1) ≠ 0)
    (hstruct : ∀ᶠ lam in atTop,
      ((∀ j, j ≤ k → 0 ≤ d lam j ∧ d lam j ≤ d lam k) ∧
        d lam k < d lam (k + 1) ∧ d lam (k + 1) < d lam (k + 2)) ∧
        ∀ j, d lam (k + 2) ≤ d lam (j + (k + 2)))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hratio : Tendsto (fun lam => d lam k / d lam (k + 1)) atTop (nhds 0))
    (htail : Tendsto (fun lam =>
      lam * d lam (k + 1) / (d lam (k + 2) - d lam (k + 1))) atTop (nhds 0))
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop (nhds (a j))) :
    Tendsto (fun lam => depthSecularRoot (d lam) (ℓ lam) k / d lam (k + 1)) atTop
      (nhds ((∑ j ∈ Finset.range (k + 1), a j ^ 2)
        / ((∑ j ∈ Finset.range (k + 1), a j ^ 2) + a (k + 1) ^ 2))) := by
  set S := ∑ j ∈ Finset.range (k + 1), a j ^ 2 with hSdef
  have hA0 : Real.sqrt S ≠ 0 := (Real.sqrt_pos.2 haS).ne'
  -- coordinate limits of the flattened family
  have hsumlim : Tendsto (fun lam => ∑ j ∈ Finset.range (k + 1), ℓ lam j ^ 2) atTop
      (nhds S) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hjk : j ≤ k + 1 :=
      le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) (Nat.le_succ k)
    exact (hl j hjk).pow 2
  have hl0D : Tendsto (fun lam => flattenedCoords (ℓ lam) k 0) atTop
      (nhds (Real.sqrt S)) := by
    have hcomp := (Real.continuous_sqrt.tendsto S).comp hsumlim
    simpa [Function.comp_def] using hcomp
  have hl1D : Tendsto (fun lam => flattenedCoords (ℓ lam) k 1) atTop (nhds (a (k + 1))) :=
    hl (k + 1) le_rfl
  -- eventual hypotheses of the flattened families
  have hsumD : ∀ᶠ lam in atTop, Summable fun j => flattenedCoords (ℓ lam) k j ^ 2 := by
    filter_upwards [hsum] with lam hsm
    exact summable_flattenedCoords_sq hsm
  have hbesselD : ∀ᶠ lam in atTop,
      (∑' j : ℕ, flattenedCoords (ℓ lam) k j ^ 2) ≤ 2 * lam := by
    filter_upwards [hsum, hbessel] with lam hsm hbes
    rw [tsum_flattenedCoords_sq hsm]
    exact hbes
  have hstructZ : ∀ᶠ lam in atTop,
      (0 ≤ flattenedScales (d lam) k 0 0 ∧
        flattenedScales (d lam) k 0 0 < flattenedScales (d lam) k 0 1 ∧
        flattenedScales (d lam) k 0 1 < flattenedScales (d lam) k 0 2) ∧
      ∀ j, flattenedScales (d lam) k 0 2 ≤ flattenedScales (d lam) k 0 (j + 2) := by
    filter_upwards [hstruct] with lam hst
    obtain ⟨⟨hhead, hk01, hk12⟩, hfloor⟩ := hst
    refine ⟨⟨le_refl 0, ?_, ?_⟩, ?_⟩
    · exact lt_of_le_of_lt (hhead k le_rfl).1 hk01
    · rw [flattenedScales_two]; exact hk12
    · intro j; rw [flattenedScales_two, flattenedScales_add_two]; exact hfloor j
  have hstructT : ∀ᶠ lam in atTop,
      (0 ≤ flattenedScales (d lam) k (d lam k) 0 ∧
        flattenedScales (d lam) k (d lam k) 0 < flattenedScales (d lam) k (d lam k) 1 ∧
        flattenedScales (d lam) k (d lam k) 1 < flattenedScales (d lam) k (d lam k) 2) ∧
      ∀ j, flattenedScales (d lam) k (d lam k) 2
        ≤ flattenedScales (d lam) k (d lam k) (j + 2) := by
    filter_upwards [hstruct] with lam hst
    obtain ⟨⟨hhead, hk01, hk12⟩, hfloor⟩ := hst
    refine ⟨⟨(hhead k le_rfl).1, hk01, ?_⟩, ?_⟩
    · rw [flattenedScales_two]; exact hk12
    · intro j; rw [flattenedScales_two, flattenedScales_add_two]; exact hfloor j
  have hratioZ : Tendsto (fun lam =>
      flattenedScales (d lam) k 0 0 / flattenedScales (d lam) k 0 1) atTop (nhds 0) :=
    tendsto_const_nhds.congr fun lam => (zero_div _).symm
  have htailZ : Tendsto (fun lam => lam * flattenedScales (d lam) k 0 1 /
      (flattenedScales (d lam) k 0 2 - flattenedScales (d lam) k 0 1)) atTop (nhds 0) := by
    refine htail.congr fun lam => ?_
    rw [flattenedScales_two]
  have htailT : Tendsto (fun lam => lam * flattenedScales (d lam) k (d lam k) 1 /
      (flattenedScales (d lam) k (d lam k) 2
        - flattenedScales (d lam) k (d lam k) 1)) atTop (nhds 0) := by
    refine htail.congr fun lam => ?_
    rw [flattenedScales_two]
  -- the two flattened root limits
  have hcheck := infiniteSecularRoot_ratio_tendsto
    (d := fun lam => flattenedScales (d lam) k 0)
    (ℓ := fun lam => flattenedCoords (ℓ lam) k)
    hA0 hak1 hstructZ hsumD hbesselD hratioZ htailZ hl0D hl1D
  have hhat := infiniteSecularRoot_ratio_tendsto
    (d := fun lam => flattenedScales (d lam) k (d lam k))
    (ℓ := fun lam => flattenedCoords (ℓ lam) k)
    hA0 hak1 hstructT hsumD hbesselD hratio htailT hl0D hl1D
  rw [Real.sq_sqrt haS.le] at hcheck hhat
  -- the lower flattened root eventually clears `d_k`
  have hw : 0 < S / (S + a (k + 1) ^ 2) :=
    div_pos haS (add_pos_of_pos_of_nonneg haS (sq_nonneg _))
  have hd1pos : ∀ᶠ lam in atTop, 0 < d lam (k + 1) := by
    filter_upwards [hstruct] with lam hst
    exact lt_of_le_of_lt (hst.1.1 k le_rfl).1 hst.1.2.1
  have hbr : ∀ᶠ lam in atTop, d lam k <
      infiniteSecularRoot (flattenedScales (d lam) k 0) (flattenedCoords (ℓ lam) k) := by
    have h1 := hcheck.eventually (eventually_gt_nhds (half_lt_self hw))
    have h2 := hratio.eventually (eventually_lt_nhds (half_pos hw))
    filter_upwards [h1, h2, hd1pos] with lam ha hb hd1
    have hlt : d lam k / d lam (k + 1) <
        infiniteSecularRoot (flattenedScales (d lam) k 0) (flattenedCoords (ℓ lam) k)
          / d lam (k + 1) := lt_trans hb ha
    have h := mul_lt_mul_of_pos_right hlt hd1
    rwa [div_mul_cancel₀ _ hd1.ne', div_mul_cancel₀ _ hd1.ne'] at h
  -- eventual nonzero coordinates
  have hSne : ∀ᶠ lam in atTop, flattenedCoords (ℓ lam) k 0 ≠ 0 := hl0D.eventually_ne hA0
  have hk1ne : ∀ᶠ lam in atTop, ℓ lam (k + 1) ≠ 0 := (hl (k + 1) le_rfl).eventually_ne hak1
  -- the bracket, eventually
  have hbracket : ∀ᶠ lam in atTop,
      infiniteSecularRoot (flattenedScales (d lam) k 0) (flattenedCoords (ℓ lam) k)
          / d lam (k + 1)
        ≤ depthSecularRoot (d lam) (ℓ lam) k / d lam (k + 1) ∧
      depthSecularRoot (d lam) (ℓ lam) k / d lam (k + 1)
        ≤ infiniteSecularRoot (flattenedScales (d lam) k (d lam k))
            (flattenedCoords (ℓ lam) k) / d lam (k + 1) := by
    filter_upwards [hstruct, hsum, hSne, hk1ne, hbr, hd1pos]
      with lam hst hsm hSn hk1n hbrl hd1
    obtain ⟨⟨hhead, hk01, hk12⟩, hfloor⟩ := hst
    obtain ⟨_, _, hlow, hhigh⟩ :=
      depthSecularRoot_bracket hk01 hk12 hfloor hhead hsm hSn hk1n hbrl
    exact ⟨div_le_div_of_le_of_pos'' hlow hd1, div_le_div_of_le_of_pos'' hhigh hd1⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hcheck hhat
    (hbracket.mono fun lam h => h.1) (hbracket.mono fun lam h => h.2)

/-- **The exact CCM ladder at every depth.**  With the Hermite coordinate limits, the exact
constrained root in the `k`-th gap obeys `μ_k(λ)/d_{k+1}(λ) → θ_k = Q_k/Q_{k+1}` — the card's
all-depth spectral fingerprint for the true infinite-dimensional constrained problem. -/
theorem ccm_depthSecularRoot_ratio_tendsto
    {d ℓ : ℝ → ℕ → ℝ} {k : ℕ}
    (hstruct : ∀ᶠ lam in atTop,
      ((∀ j, j ≤ k → 0 ≤ d lam j ∧ d lam j ≤ d lam k) ∧
        d lam k < d lam (k + 1) ∧ d lam (k + 1) < d lam (k + 2)) ∧
        ∀ j, d lam (k + 2) ≤ d lam (j + (k + 2)))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hratio : Tendsto (fun lam => d lam k / d lam (k + 1)) atTop (nhds 0))
    (htail : Tendsto (fun lam =>
      lam * d lam (k + 1) / (d lam (k + 2) - d lam (k + 1))) atTop (nhds 0))
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun lam => depthSecularRoot (d lam) (ℓ lam) k / d lam (k + 1)) atTop
      (nhds (constrainedProlateHermiteTheta k)) := by
  have haS : 0 < ∑ j ∈ Finset.range (k + 1), constrainedProlateHermiteCoordinate j ^ 2 :=
    constrainedProlateHermiteSquareSum_pos k
  have hak1 : constrainedProlateHermiteCoordinate (k + 1) ≠ 0 :=
    constrainedProlateHermiteCoordinate_ne_zero (k + 1)
  have h := depthSecularRoot_ratio_tendsto haS hak1 hstruct hsum hbessel hratio htail hl
  have hθ : (∑ j ∈ Finset.range (k + 1), constrainedProlateHermiteCoordinate j ^ 2)
      / ((∑ j ∈ Finset.range (k + 1), constrainedProlateHermiteCoordinate j ^ 2)
        + constrainedProlateHermiteCoordinate (k + 1) ^ 2)
      = constrainedProlateHermiteTheta k := by
    have hsq := constrainedProlateHermiteTheta_eq_square_ratio k
    rwa [Real.sq_sqrt (constrainedProlateHermiteSquareSum_pos k).le] at hsq
  rwa [hθ] at h

end RHTower
