/-
# The Schatten norms and their Hölder inequality

The Schatten `p`-norm is the `ℓ^p` norm of the approximation numbers.  Submultiplicativity of those
numbers, together with Hölder for series, gives the quantitative Hölder inequality on the scale,
with the only loss the factor coming from the two-fold index shift.

Main results:
* `tsum_comp_nat_div_le` — the tsum companion of the `k`-fold repetition bound.
* `schattenNorm`, `schattenNorm_nonneg`, `schattenNorm_one_eq_traceNorm` — the norm.
* `tsum_rpow_approxNumber_comp_le` — **Hölder in the `r`-th power form**.
* `schattenNorm_comp_le` — **Hölder for the Schatten norms**.
-/
import GaloisForLFunctions.HTGeometry.SchattenHolder

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-- The tsum companion of the `k`-fold repetition bound. -/
theorem tsum_comp_nat_div_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hs : Summable f)
    {k : ℕ} (hk : 0 < k) : ∑' m : ℕ, f (m / k) ≤ (k : ℝ) * ∑' n, f n := by
  classical
  refine Real.tsum_le_of_sum_range_le (fun m => hf _) fun N => ?_
  have hmaps : ∀ m ∈ Finset.range N, m / k ∈ Finset.range N := by
    intro m hm
    exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.div_le_self m k) (Finset.mem_range.mp hm))
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps (fun m => f (m / k))
  rw [← hfiber]
  have hcard : ∀ n ∈ Finset.range N,
      ((Finset.range N).filter fun m => m / k = n).card ≤ k := by
    intro n _
    have hsub : ((Finset.range N).filter fun m => m / k = n)
        ⊆ Finset.Ico (k * n) (k * n + k) := by
      intro m hm
      have hmk : m / k = n := (Finset.mem_filter.mp hm).2
      have hdm := Nat.div_add_mod m k
      have hlt := Nat.mod_lt m hk
      rw [hmk] at hdm
      refine Finset.mem_Ico.mpr ⟨?_, ?_⟩ <;> omega
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Nat.card_Ico]
    omega
  have hstep : ∀ n ∈ Finset.range N,
      (∑ m ∈ (Finset.range N).filter fun m => m / k = n, f (m / k)) ≤ (k : ℝ) * f n := by
    intro n hn
    have hconst : (∑ m ∈ (Finset.range N).filter fun m => m / k = n, f (m / k))
        = (((Finset.range N).filter fun m => m / k = n).card : ℝ) * f n := by
      rw [Finset.sum_congr rfl fun m hm => by rw [(Finset.mem_filter.mp hm).2], Finset.sum_const,
        nsmul_eq_mul]
    rw [hconst]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard n hn) (hf n)
  calc (∑ n ∈ Finset.range N, ∑ m ∈ (Finset.range N).filter fun m => m / k = n, f (m / k))
      ≤ ∑ n ∈ Finset.range N, (k : ℝ) * f n := Finset.sum_le_sum hstep
    _ = (k : ℝ) * ∑ n ∈ Finset.range N, f n := by rw [Finset.mul_sum]
    _ ≤ (k : ℝ) * ∑' n, f n := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => hf n)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Schatten `p`-norm: the `ℓ^p` norm of the approximation numbers. -/
def schattenNorm (p : ℝ) (T : H →L[ℂ] H) : ℝ := (∑' n, approxNumber T n ^ p) ^ (1 / p)

omit [CompleteSpace H] in
theorem schattenNorm_nonneg (p : ℝ) (T : H →L[ℂ] H) : 0 ≤ schattenNorm p T :=
  Real.rpow_nonneg (tsum_nonneg fun n => Real.rpow_nonneg (approxNumber_nonneg T n) p) _

omit [CompleteSpace H] in
theorem schattenNorm_one_eq_traceNorm (T : H →L[ℂ] H) :
    schattenNorm 1 T = traceNorm H T := by
  rw [schattenNorm, traceNorm, div_one, Real.rpow_one]
  exact tsum_congr fun n => Real.rpow_one _

omit [CompleteSpace H] in
/-- **Hölder in the `r`-th power form.** -/
theorem tsum_rpow_approxNumber_comp_le {p q r : ℝ} (hpqr : Real.HolderTriple p q r)
    {S T : H →L[ℂ] H} (hS : MemSchattenClass p S) (hT : MemSchattenClass q T) :
    ∑' m, approxNumber (S ∘L T) m ^ r
      ≤ 2 * ((∑' n, approxNumber S n ^ p) ^ (r / p)
        * (∑' n, approxNumber T n ^ q) ^ (r / q)) := by
  have hr0 : 0 < r := hpqr.pos'
  have hcoe : ∀ (x s : ℝ), 0 ≤ x → ((Real.toNNReal x ^ s : NNReal) : ℝ) = x ^ s := by
    intro x s hx
    rw [NNReal.coe_rpow, Real.coe_toNNReal x hx]
  have hf : Summable fun n : ℕ => (Real.toNNReal (approxNumber S n)) ^ p := by
    rw [← NNReal.summable_coe]
    exact hS.congr fun n => (hcoe _ _ (approxNumber_nonneg S n)).symm
  have hg : Summable fun n : ℕ => (Real.toNNReal (approxNumber T n)) ^ q := by
    rw [← NNReal.summable_coe]
    exact hT.congr fun n => (hcoe _ _ (approxNumber_nonneg T n)).symm
  have hprod : Summable fun n : ℕ => (approxNumber S n * approxNumber T n) ^ r := by
    have hc := NNReal.summable_coe.mpr (NNReal.summable_mul_rpow_of_Lp_Lq hpqr hf hg)
    refine hc.congr fun n => ?_
    rw [NNReal.coe_rpow, NNReal.coe_mul, Real.coe_toNNReal _ (approxNumber_nonneg S n),
      Real.coe_toNNReal _ (approxNumber_nonneg T n)]
  have hcomp : MemSchattenClass r (S ∘L T) := memSchattenClass_comp hpqr hS hT
  have hpt : ∀ m : ℕ, approxNumber (S ∘L T) m ^ r
      ≤ (approxNumber S (m / 2) * approxNumber T (m / 2)) ^ r := by
    intro m
    have h1 : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
    have h2 := approxNumber_antitone (S ∘L T) h1
    have h3 : approxNumber (S ∘L T) (m / 2 + m / 2)
        ≤ approxNumber S (m / 2) * approxNumber T (m / 2) :=
      approxNumber_comp_add_le S T (m / 2) (m / 2)
    have hidx : m / 2 + m / 2 = 2 * (m / 2) := by ring
    rw [hidx] at h3
    exact Real.rpow_le_rpow (approxNumber_nonneg _ m) (le_trans h2 h3) hr0.le
  have hrep : Summable fun m : ℕ => (approxNumber S (m / 2) * approxNumber T (m / 2)) ^ r :=
    summable_comp_nat_div
      (fun n => Real.rpow_nonneg
        (mul_nonneg (approxNumber_nonneg S n) (approxNumber_nonneg T n)) r)
      hprod (by norm_num : 0 < 2)
  have hstep1 : ∑' m, approxNumber (S ∘L T) m ^ r
      ≤ ∑' m, (approxNumber S (m / 2) * approxNumber T (m / 2)) ^ r :=
    hcomp.tsum_le_tsum hpt hrep
  have hstep2 : (∑' m, (approxNumber S (m / 2) * approxNumber T (m / 2)) ^ r)
      ≤ (2 : ℝ) * ∑' n, (approxNumber S n * approxNumber T n) ^ r := by
    have := tsum_comp_nat_div_le
      (fun n => Real.rpow_nonneg
        (mul_nonneg (approxNumber_nonneg S n) (approxNumber_nonneg T n)) r)
      hprod (by norm_num : 0 < 2)
    simpa using this
  have hstep3 : ∑' n, (approxNumber S n * approxNumber T n) ^ r
      ≤ (∑' n, approxNumber S n ^ p) ^ (r / p) * (∑' n, approxNumber T n ^ q) ^ (r / q) := by
    have hNN := NNReal.Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg
    have hcast := (NNReal.coe_le_coe (r₁ := _) (r₂ := _)).mpr hNN
    rw [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_rpow, NNReal.coe_tsum, NNReal.coe_tsum,
      NNReal.coe_tsum] at hcast
    refine le_trans (le_of_eq ?_) (le_trans hcast (le_of_eq ?_))
    · exact tsum_congr fun n => by
        rw [← hcoe _ r (mul_nonneg (approxNumber_nonneg S n) (approxNumber_nonneg T n))]
        congr 1
        rw [← Real.toNNReal_mul (approxNumber_nonneg S n)]
    · have hS' : (∑' n : ℕ, ((Real.toNNReal (approxNumber S n) ^ p : NNReal) : ℝ))
          = ∑' n, approxNumber S n ^ p :=
        tsum_congr fun n => hcoe _ _ (approxNumber_nonneg S n)
      have hT' : (∑' n : ℕ, ((Real.toNNReal (approxNumber T n) ^ q : NNReal) : ℝ))
          = ∑' n, approxNumber T n ^ q :=
        tsum_congr fun n => hcoe _ _ (approxNumber_nonneg T n)
      rw [hS', hT']
  linarith [hstep1, hstep2, hstep3,
    mul_le_mul_of_nonneg_left hstep3 (by norm_num : (0:ℝ) ≤ 2)]

omit [CompleteSpace H] in
/-- **Hölder for the Schatten norms.** -/
theorem schattenNorm_comp_le {p q r : ℝ} (hpqr : Real.HolderTriple p q r)
    {S T : H →L[ℂ] H} (hS : MemSchattenClass p S) (hT : MemSchattenClass q T) :
    schattenNorm r (S ∘L T) ≤ (2 : ℝ) ^ (1 / r) * (schattenNorm p S * schattenNorm q T) := by
  have hr0 : 0 < r := hpqr.pos'
  have hp0 : 0 < p := hpqr.left_pos
  have hq0 : 0 < q := hpqr.right_pos
  have h1r : (0 : ℝ) ≤ 1 / r := le_of_lt (one_div_pos.mpr hr0)
  set X : ℝ := ∑' n, approxNumber S n ^ p with hXdef
  set Y : ℝ := ∑' n, approxNumber T n ^ q with hYdef
  have hX0 : 0 ≤ X := tsum_nonneg fun n => Real.rpow_nonneg (approxNumber_nonneg S n) p
  have hY0 : 0 ≤ Y := tsum_nonneg fun n => Real.rpow_nonneg (approxNumber_nonneg T n) q
  have hbase := tsum_rpow_approxNumber_comp_le hpqr hS hT
  have hmono : (∑' m, approxNumber (S ∘L T) m ^ r) ^ (1 / r)
      ≤ (2 * (X ^ (r / p) * Y ^ (r / q))) ^ (1 / r) :=
    Real.rpow_le_rpow (tsum_nonneg fun m => Real.rpow_nonneg (approxNumber_nonneg _ m) r)
      hbase h1r
  refine le_trans hmono (le_of_eq ?_)
  have hXr : (0 : ℝ) ≤ X ^ (r / p) := Real.rpow_nonneg hX0 _
  have hYr : (0 : ℝ) ≤ Y ^ (r / q) := Real.rpow_nonneg hY0 _
  rw [Real.mul_rpow (by norm_num) (mul_nonneg hXr hYr), Real.mul_rpow hXr hYr,
    ← Real.rpow_mul hX0, ← Real.rpow_mul hY0]
  have hexp1 : r / p * (1 / r) = 1 / p := by field_simp
  have hexp2 : r / q * (1 / r) = 1 / q := by field_simp
  rw [hexp1, hexp2, schattenNorm, schattenNorm]

end

end GaloisForLFunctions.HTGeometry
