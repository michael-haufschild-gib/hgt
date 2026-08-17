import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse

/-!
# The sharp rank--energy law for low spectral moments

A finite spectral packet of rank `R` and Schatten-`p` energy `E` can carry a `k`-th moment of size
at most `R^{1-k/p} E^k`: this is Hölder against the counting measure, and it is attained exactly
when all the moduli are equal -- the root-of-unity micro-spectra.

Read backwards, retaining a moment of size `c` while the energy shrinks to `ε` forces the rank to
grow like `(c/ε^k)^{p/(p-k)}`.  At `k = p` the exponent degenerates and no vanishing packet can
retain its moment, so the cutoff at `p-1` is forced quantitatively.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

section RankEnergy

variable {ι : Type*}

/-- **`(RE)`: the rank--energy bound.**  A nonnegative spectral packet has `k`-th power sum at most
the rank to the power `1 - k/p` times the `p`-th power sum to the power `k/p`. -/
theorem sum_rpow_le_card_rpow_mul (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {k p : ℝ} (hk : 0 < k) (hkp : k ≤ p) (hs : s.Nonempty) :
    ∑ i ∈ s, a i ^ k ≤ (s.card : ℝ) ^ (1 - k / p) * (∑ i ∈ s, a i ^ p) ^ (k / p) := by
  have hp : 0 < p := lt_of_lt_of_le hk hkp
  have hR : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  set R : ℝ := (s.card : ℝ) with hRdef
  set X : ℝ := ∑ i ∈ s, a i ^ k with hX
  set Y : ℝ := ∑ i ∈ s, a i ^ p with hY
  have hXnn : 0 ≤ X := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) k
  have hYnn : 0 ≤ Y := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) p
  have hweight : ∑ _i ∈ s, (1 / R) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hRdef]
    field_simp
  have hjensen := Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => 1 / R) (fun i => a i ^ k)
    (fun i _ => by positivity) hweight (fun i hi => Real.rpow_nonneg (ha i hi) k)
    (p := p / k) (by rw [le_div_iff₀ hk]; linarith)
  have hpow : ∀ i ∈ s, ((a i ^ k) ^ (p / k) : ℝ) = a i ^ p := by
    intro i hi
    rw [← Real.rpow_mul (ha i hi)]
    congr 1
    field_simp
  have hleft : ∑ i ∈ s, (1 / R) * a i ^ k = X / R := by
    rw [← Finset.mul_sum, hX]
    ring
  have hright : ∑ i ∈ s, (1 / R) * (a i ^ k) ^ (p / k) = Y / R := by
    rw [Finset.sum_congr rfl fun i hi => by rw [hpow i hi], ← Finset.mul_sum, hY]
    ring
  rw [hleft, hright] at hjensen
  -- take the `k/p`-th power of both sides
  have hkp0 : 0 < k / p := by positivity
  have hmono : ((X / R) ^ (p / k)) ^ (k / p) ≤ (Y / R) ^ (k / p) :=
    Real.rpow_le_rpow (by positivity) hjensen (le_of_lt hkp0)
  have hcancel : ((X / R) ^ (p / k)) ^ (k / p) = X / R := by
    rw [← Real.rpow_mul (by positivity)]
    rw [show p / k * (k / p) = 1 by field_simp]
    exact Real.rpow_one _
  rw [hcancel] at hmono
  have hstep : X ≤ R * (Y / R) ^ (k / p) := by
    have hd := (div_le_iff₀ hR).mp hmono
    linarith [hd]
  refine le_trans hstep (le_of_eq ?_)
  rw [Real.div_rpow hYnn (le_of_lt hR), Real.rpow_sub hR, Real.rpow_one]
  field_simp

/-- **Equality for a flat packet.**  A packet whose moduli are all equal attains the bound. -/
theorem sum_rpow_const (s : Finset ι) {c k : ℝ} :
    ∑ _i ∈ s, c ^ k = (s.card : ℝ) * c ^ k := by
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **The forced rank scale.**  Retaining a `k`-th moment of size `c` at energy `ε` forces the rank
above `(c / ε^k)^{p/(p-k)}`. -/
theorem card_rpow_ge_of_moment (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {k p c ε : ℝ} (hk : 0 < k) (hkp : k < p) (hs : s.Nonempty)
    (hmoment : c ≤ ∑ i ∈ s, a i ^ k) (henergy : ∑ i ∈ s, a i ^ p ≤ ε ^ p) :
    c ≤ (s.card : ℝ) ^ (1 - k / p) * (ε ^ p) ^ (k / p) := by
  have hp : 0 < p := lt_trans hk hkp
  refine le_trans hmoment (le_trans (sum_rpow_le_card_rpow_mul s a ha hk (le_of_lt hkp) hs) ?_)
  have hbase : (0 : ℝ) ≤ ∑ i ∈ s, a i ^ p :=
    Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) p
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) ^ (1 - k / p) := Real.rpow_nonneg (by positivity) _
  refine mul_le_mul_of_nonneg_left ?_ hcard
  exact Real.rpow_le_rpow hbase henergy (by positivity)

/-- **The cutoff is forced.**  At `k = p` the rank factor is one, so no rank can amplify a moment
against a vanishing energy. -/
theorem card_rpow_eq_one_of_eq {R p : ℝ} (hp : 0 < p) :
    R ^ (1 - p / p) = 1 := by
  rw [div_self (ne_of_gt hp), sub_self, Real.rpow_zero]

end RankEnergy

section Cost

/-- **The Schatten cost of a degree-`k` micro-spectrum block.**  A block of `k * N` eigenvalues of
modulus `|t|` with `|t|^k = |c| / (k * N)` costs `(k*N)^{1 - p/k} * |c|^{p/k}` in Schatten-`p`
energy. -/
theorem block_cost (kN : ℝ) (hkN : 0 < kN) {c t p k : ℝ} (hk : 0 < k) (ht : 0 ≤ t)
    (htc : t ^ k = c / kN) (hc : 0 ≤ c) :
    kN * t ^ p = kN ^ (1 - p / k) * c ^ (p / k) := by
  have hkc : (t ^ k) ^ (p / k) = t ^ p := by
    rw [← Real.rpow_mul ht]
    congr 1
    field_simp
  calc kN * t ^ p = kN * (t ^ k) ^ (p / k) := by rw [hkc]
    _ = kN * (c / kN) ^ (p / k) := by rw [htc]
    _ = kN ^ (1 - p / k) * c ^ (p / k) := by
        rw [Real.div_rpow hc (le_of_lt hkN), Real.rpow_sub hkN, Real.rpow_one]
        field_simp

end Cost

end GaloisForLFunctions.HTGeometry
