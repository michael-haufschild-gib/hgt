import GaloisForLFunctions.RestrictedFactorizationCalculus.TheAbsoluteCostOfTheFourSeventhsInterior
import GaloisForLFunctions.RestrictedFactorizationCalculus.LogarithmicSavingsThroughoutTheRoughInterior

/-!
# Opposite signed masses in the prime-power interior

The transposed row has almost two units of absolute mass per unit cutoff
and its signed sum loses every fixed logarithmic power. Consequently both
signs occur with almost one unit of mass each. Sign-aligned relative
errors of inverse-logarithmic size can force either sign uniformly.
-/
noncomputable section
open Filter Finset ArithmeticFunction
open scoped Topology Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev atom (y X T q : ℕ) := roughMangoldtWeight y q*interiorKernel y X T q
private abbrev S (y X T : ℕ) := roughInteriorReading (roughMangoldtWeight y) y X T

/-- Total mass of one orientation of the transposed prime-power increments. -/
def orientedInteriorMass (σ : ℝ) (y X T : ℕ) :=
  ∑ q∈Icc 1 X,max (σ*atom y X T q) 0

private theorem twice_oriented (y X T : ℕ) :
    2*orientedInteriorMass 1 y X T=absoluteRoughInterior y X T+S y X T ∧
    2*orientedInteriorMass (-1) y X T=absoluteRoughInterior y X T-S y X T := by
  have plus (x : ℝ) : 2*max x 0=|x|+x := by
    rcases le_total 0 x with h|h
    · rw [max_eq_left h,abs_of_nonneg h]; ring
    · rw [max_eq_right h,abs_of_nonpos h]; ring
  have minus (x : ℝ) : 2*max (-x) 0=|x|-x := by rw [plus,abs_neg,sub_eq_add_neg]
  simp only [S,rough_interior_as_kernel,orientedInteriorMass,absoluteRoughInterior,
    mul_sum,←sum_add_distrib,←sum_sub_distrib,one_mul,neg_one_mul]
  exact ⟨sum_congr rfl (fun q _ => plus (atom y X T q)),sum_congr rfl (fun q _ => minus (atom y X T q))⟩

private theorem saving_small (p : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ T : ℕ, |S (logSquareCutoff X) X T| * Real.log X^p ≤ δ*(X:ℝ) := by
  obtain ⟨K,hK,h⟩ := uniform_log_savings_for_mangoldt_interiors (p+1)
  have growth := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h,logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,
    growth.eventually_ge_atTop (K/δ),eventually_ge_atTop 2] with X hx hy hlog hX
  intro T
  have hl : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hh := hx _ hy le_rfl T
  have hK' := (div_le_iff₀ hδ).mp hlog
  apply (mul_le_mul_iff_left₀ hl).mp
  calc |S _ X T| * Real.log X^p*Real.log X ≤ K*(X:ℝ) := by simpa only [pow_succ,mul_assoc] using hh
       _ ≤ (Real.log X*δ)*(X:ℝ) := mul_le_mul_of_nonneg_right hK' (Nat.cast_nonneg X)
       _ = _ := by ring

/-- Each sign separately carries at least (1−ε)X at every sublinear
head, including the four-sevenths cutoff. -/
theorem both_orientations_after_sublinear_heads {α ε : ℝ} (ha : 0 ≤ α) (h1 : α < 1) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ T : ℕ,(T:ℝ) ≤ (X:ℝ)^α →
      let y := logSquareCutoff X
      (1-ε)*(X:ℝ) ≤ min (orientedInteriorMass 1 y X T) (orientedInteriorMass (-1) y X T) := by
  filter_upwards [absolute_price_after_sublinear_prime_head ha h1 hε,saving_small 0 hε]
    with X habs hs
  intro T hT
  have h := hs T
  rw [pow_zero,mul_one] at h
  obtain ⟨hp,hn⟩ := twice_oriented (logSquareCutoff X) X T
  have hv := habs T hT
  apply le_min <;> linarith only [hp,hn,hv,(abs_le.mp h).1,(abs_le.mp h).2]

/-- Signed rough prime powers perturbed independently at each increment. -/
def relativeInteriorWeight (y : ℕ) (e : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun q => (1+e q)*roughMangoldtWeight y q,by simp⟩

private theorem endpoint (y X T : ℕ) (t : ℝ) :
    ∃ e : ℕ → ℝ, (∀ q,|e q| ≤ |t|) ∧
      roughInteriorReading (relativeInteriorWeight y e) y X T=S y X T+t*absoluteRoughInterior y X T := by
  let e := fun q => if 0 ≤ atom y X T q then t else -t
  refine ⟨e,fun q => ?_,?_⟩
  · dsimp only [e];split <;> simp
  · simp only [S,rough_interior_as_kernel,absoluteRoughInterior,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro q _
    change (1+e q)*roughMangoldtWeight y q*interiorKernel y X T q=
      atom y X T q+t*|atom y X T q|
    rw [mul_assoc]
    change (1+e q)*atom y X T q=_
    dsimp only [e]
    split_ifs with h
    · rw [abs_of_nonneg h];ring
    · rw [abs_of_neg (lt_of_not_ge h)];ring

/-- Even coordinatewise relative errors of size 1/log(X)^p attain both
signs at scale X/log(X)^p, uniformly after removing any sublinear power head. -/
theorem opposite_readings_under_inverse_log_errors (p : ℕ) {α : ℝ} (ha : 0 ≤ α) (h1 : α < 1) :
    ∀ᶠ X : ℕ in atTop, ∀ T : ℕ,(T:ℝ) ≤ (X:ℝ)^α →
      let L := Real.log (X:ℝ)^p
      let y := logSquareCutoff X
      ∃ e f : ℕ → ℝ, (∀ q,|e q| ≤ 1/L ∧ |f q| ≤ 1/L) ∧
        (X:ℝ)/L ≤ roughInteriorReading (relativeInteriorWeight y e) y X T ∧
        roughInteriorReading (relativeInteriorWeight y f) y X T ≤ -((X:ℝ)/L) := by
  filter_upwards [absolute_price_after_sublinear_prime_head ha h1 (by norm_num : (0:ℝ) < 1/2),
    saving_small p (by norm_num : (0:ℝ) < 1/2),eventually_ge_atTop 2] with X habs hs hX
  intro T hT
  let y := logSquareCutoff X
  let L := Real.log (X:ℝ)^p
  have hL : 0 < L := pow_pos (Real.log_pos (by exact_mod_cast (show 1 < X by omega))) _
  have hi := habs T hT
  have hnat := hs T
  change |S y X T| * L ≤ (1/2)*(X:ℝ) at hnat
  obtain ⟨e,he,hp⟩ := endpoint y X T (1/L)
  obtain ⟨f,hf,hn⟩ := endpoint y X T (-(1/L))
  have low : -(1/2*(X:ℝ)) ≤ S y X T*L := by
    rw [←abs_of_pos hL,←abs_mul] at hnat
    exact (abs_le.mp hnat).1
  have high : S y X T*L ≤ (1/2)*(X:ℝ) := by
    rw [←abs_of_pos hL,←abs_mul] at hnat
    exact (abs_le.mp hnat).2
  refine ⟨e,f,fun q => ⟨by simpa only [abs_of_pos (one_div_pos.mpr hL)] using he q,
    by simpa only [abs_neg,abs_of_pos (one_div_pos.mpr hL)] using hf q⟩,?_,?_⟩
  · rw [hp,div_le_iff₀ hL,add_mul,one_div_mul_eq_div,div_mul_cancel₀ _ hL.ne']
    linarith only [low,hi]
  · change roughInteriorReading (relativeInteriorWeight y f) y X T ≤ -((X:ℝ)/L)
    rw [hn,show -((X:ℝ)/L)=(-(X:ℝ))/L by ring,le_div_iff₀ hL,add_mul]
    rw [show (-(1/L)*absoluteRoughInterior y X T)*L = -absoluteRoughInterior y X T by
      field_simp [hL.ne']]
    linarith only [high,hi]

end GaloisForLFunctions.RestrictedFactorizationCalculus
