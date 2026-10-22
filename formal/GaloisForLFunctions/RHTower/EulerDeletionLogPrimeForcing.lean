import GaloisForLFunctions.RHTower.EulerDeletionCenteredCellWindow
import GaloisForLFunctions.RHTower.EulerDeletionMobiusGramCancellation
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.Analysis.Normed.Group.Tannery
import GaloisForLFunctions.RHTower.Deninger.DeningerVonMangoldtMoebiusConvolution
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap

/-!
# Compulsory forcing in compensated logarithmic renewal

The original compensated source has prime-dilation feedback together with a
harmonic correction from every earlier cutoff. `compensated_renewal` retains
both terms exactly in the existing physical carrier.

The correction has squared norm comparable to the cutoff. Its positive cell
mean follows from a signed hyperbola sum, the prime number theorem, and
summable domination. The physical-window inequality supplies the lower
energy bound; finite Abel summation supplies the upper bound.

These unconditional results rule out discarding the correction as a
subpower error. They do not bound the joint signed residual at the RH
threshold, prove RH, or falsify RH.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology Finset ArithmeticFunction
open scoped BigOperators
namespace RHTower.DeletionLogPrimeForcing

/-- Literal harmonic compensation coefficient at each prime-power scale. -/
def coeff (N q : ℕ) : ℝ := vonMangoldt q * deningerHarmonicPartial (N / q)
/-- The complete correction in the original physical Hilbert carrier. -/
def forcing (N : ℕ) : BDCarrier := DeletionCoefficientTransfer.source (coeff N) N
/-- The absolutely convergent signed reciprocal-square Mobius series. -/
def c2 : ℝ := ∑' n : ℕ, ((moebius (n+1) : ℤ) : ℝ) / ((n : ℝ)+1)^(2 : ℕ)
private def Cpsi : ℝ := Real.log 4 + 4

private theorem Cpsi_pos : 0 < Cpsi := by
  unfold Cpsi
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  linarith

private theorem psi_bound (x : ℝ) (hx : 0 ≤ x) : Chebyshev.psi x ≤ Cpsi*x :=
  Chebyshev.psi_le_const_mul_self hx

private theorem harmonic_bound (N : ℕ) : |deningerHarmonicPartial N| ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [deningerHarmonicPartial]
  have h := abs_one_sub_bdMobiusModularApproximant_le N N
  rw [one_sub_bdMobiusModularApproximant N N hN le_rfl, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg N)] at h
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

private theorem inverse_square_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^(2 : ℕ)) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1/(n : ℝ)^(2 : ℕ)) 1).2
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  simpa only [Nat.cast_add, Nat.cast_one] using h

private theorem c2_summable :
    Summable (fun n : ℕ => ((moebius (n+1) : ℤ) : ℝ)/((n : ℝ)+1)^(2 : ℕ)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ inverse_square_summable
  intro n
  simp only [Real.norm_eq_abs, abs_div,
    abs_of_nonneg (sq_nonneg ((n : ℝ)+1))]
  exact div_le_div_of_nonneg_right (Sieve.abs_moebius_real_le_one _) (sq_nonneg _)

private theorem c2_prefix_lower (n : ℕ) :
    1/4 + 1/((n : ℝ)+2) ≤
      ∑ d ∈ Icc 1 (n+2), ((moebius d : ℤ) : ℝ)/(d : ℝ)^(2 : ℕ) := by
  induction n with
  | zero =>
      norm_num [Finset.sum_Icc_succ_top, moebius_apply_prime Nat.prime_two]
  | succ n ih =>
      rw [show n+1+2 = (n+2)+1 by omega, sum_Icc_succ_top (by omega)]
      have hmu := (abs_le.mp (Sieve.abs_moebius_real_le_one (n+3))).1
      have hterm : -(1/((n : ℝ)+3)^(2 : ℕ)) ≤
          ((moebius (n+2+1) : ℤ) : ℝ)/((n+2+1 : ℕ) : ℝ)^(2 : ℕ) := by
        have h := div_le_div_of_nonneg_right hmu (sq_nonneg ((n : ℝ)+3))
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
          show (n : ℝ)+2+1 = (n : ℝ)+3 by ring, neg_div, one_div] using h
      have hgap : 1/((n : ℝ)+2)-1/((n : ℝ)+3) =
          1/(((n : ℝ)+2)*((n : ℝ)+3)) := by field_simp; ring
      have hrec : 1/((n : ℝ)+3)^(2 : ℕ) ≤ 1/(((n : ℝ)+2)*((n : ℝ)+3)) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hterm ⊢
      have he : (n : ℝ)+1+2 = (n : ℝ)+3 := by ring
      rw [he]
      rw [show (n : ℝ)+2+1 = (n : ℝ)+3 by ring] at hterm ⊢
      linarith

/-- An analytic positive lower bound, without evaluating the infinite series. -/
theorem c2_lower : 1/4 ≤ c2 := by
  have hlim := c2_summable.hasSum.tendsto_sum_nat
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 2] with N hN
  have h := c2_prefix_lower (N-2)
  rw [show N-2+2=N by omega, sum_Icc_eq_sum_range_shift] at h
  have he (n : ℕ) : ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by norm_cast
  simp only [he] at h
  exact le_trans (le_add_of_nonneg_right (by positivity)) h

private def muHarmonicAF : ArithmeticFunction ℝ :=
  ⟨fun n => ((moebius n : ℤ) : ℝ)/(n : ℝ), by simp⟩

/-- Finite signed hyperbola interchange for the literal forcing coefficients. -/
theorem coeff_sum_eq_hyperbola (N : ℕ) :
    (∑ q ∈ Icc 1 N, coeff N q) =
      ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ)/(d : ℝ)*
        Chebyshev.psi ((N/d : ℕ) : ℝ) := by
  have hH (K : ℕ) : deningerHarmonicPartial K =
      ∑ m ∈ Icc 1 K, muHarmonicAF m := deningerHarmonicPartial_eq_sum_Icc K
  simp only [coeff, hH]
  rw [← sum_Icc_mul_apply vonMangoldt muHarmonicAF, mul_comm,
    sum_Icc_mul_apply]
  apply sum_congr rfl
  intro d hd
  simp only [muHarmonicAF]
  congr 1
  rw [psi_natCast_eq_sum_range, sum_Icc_eq_sum_range_shift]

private theorem psi_dilated_limit {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => Chebyshev.psi ((N/d : ℕ) : ℝ)/(N : ℝ))
      atTop (𝓝 (1/(d : ℝ))) := by
  have h1 := tendsto_psi_natCast_div.comp
    (GaloisForLFunctions.HTGeometry.tendsto_natDiv_atTop hd)
  have h2 := GaloisForLFunctions.HTGeometry.tendsto_natDiv_div_self hd
  have h := h1.mul h2
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop d] with N hN
  have hq : 0 < (N/d : ℕ) := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hN)
  have hqr : ((N/d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [Function.comp_apply]
  field_simp

private theorem psi_dilated_bound (N d : ℕ) (hd : 0 < d) :
    Chebyshev.psi ((N/d : ℕ) : ℝ)/(N : ℝ) ≤ Cpsi/(d : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using div_nonneg Cpsi_pos.le (Nat.cast_nonneg d)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hq : ((N/d : ℕ) : ℝ)*(d : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N d
  calc
    _ ≤ Cpsi*((N/d : ℕ) : ℝ)/(N : ℝ) :=
      div_le_div_of_nonneg_right (psi_bound _ (Nat.cast_nonneg _)) hNr.le
    _ ≤ _ := by
      apply (div_le_div_iff₀ hNr hdr).mpr
      nlinarith [mul_le_mul_of_nonneg_left hq Cpsi_pos.le]

/-- The forcing coefficients have a nonzero linear summatory main term. -/
theorem coeff_sum_limit :
    Tendsto (fun N : ℕ => (∑ q ∈ Icc 1 N, coeff N q)/(N : ℝ))
      atTop (𝓝 c2) := by
  let row (N n : ℕ) : ℝ :=
    ((moebius (n+1) : ℤ) : ℝ)/((n : ℝ)+1)*
      (Chebyshev.psi ((N/(n+1) : ℕ) : ℝ)/(N : ℝ))
  have hrow (n : ℕ) : Tendsto (fun N => row N n) atTop
      (𝓝 (((moebius (n+1) : ℤ) : ℝ)/((n : ℝ)+1)^(2 : ℕ))) := by
    have h := (psi_dilated_limit (by omega : 0 < n+1)).const_mul
      (((moebius (n+1) : ℤ) : ℝ)/((n : ℝ)+1))
    have he : ((moebius (n+1) : ℤ) : ℝ)/((n : ℝ)+1)*
        (1/((n+1 : ℕ) : ℝ)) =
        ((moebius (n+1) : ℤ) : ℝ)/((n : ℝ)+1)^(2 : ℕ) := by
      push_cast
      field_simp
    rw [he] at h
    exact h
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      ‖row N n‖ ≤ Cpsi*(1/((n : ℝ)+1)^(2 : ℕ)) := by
    filter_upwards with N n
    have hnon : 0 ≤ Chebyshev.psi ((N/(n+1) : ℕ) : ℝ)/(N : ℝ) :=
      div_nonneg (Chebyshev.psi_nonneg _) (Nat.cast_nonneg _)
    have hbound := psi_dilated_bound N (n+1) (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at hbound
    dsimp only [row]
    simp only [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)+1), abs_of_nonneg hnon]
    calc
      _ ≤ (1/((n : ℝ)+1))*(Cpsi/((n : ℝ)+1)) :=
        mul_le_mul (div_le_div_of_nonneg_right
          (Sieve.abs_moebius_real_le_one _) (by positivity)) hbound hnon (by positivity)
      _ = _ := by field_simp
  have hlim := tendsto_tsum_of_dominated_convergence
    (inverse_square_summable.mul_left Cpsi) hrow hdom
  apply hlim.congr'
  filter_upwards with N
  rw [coeff_sum_eq_hyperbola, sum_Icc_eq_sum_range_shift, Finset.sum_div]
  rw [tsum_eq_sum (s := range N)]
  · apply sum_congr rfl
    intro n hn
    simp only [row, Nat.cast_add, Nat.cast_one]
    ring
  · intro n hn
    have hdiv : N/(n+1)=0 := Nat.div_eq_of_lt (by
      have : ¬ n < N := by simpa only [mem_range] using hn
      omega)
    simp [row, hdiv, Chebyshev.psi_eq_sum_Icc]

private theorem coeff_partial_abs_le (N K : ℕ) :
    DeletionCoefficientTransfer.partialSum (fun q => |coeff N q|) K ≤
      (2*Cpsi)*(K : ℝ) := by
  simp only [DeletionCoefficientTransfer.partialSum]
  rw [← sum_Icc_eq_sum_range_shift (fun q => |coeff N q|) K]
  calc
    _ ≤ ∑ q ∈ Icc 1 K, 2*vonMangoldt q := by
      apply sum_le_sum
      intro q hq
      rw [coeff, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
      nlinarith [mul_le_mul_of_nonneg_left (harmonic_bound (N/q))
        (vonMangoldt_nonneg : 0 ≤ vonMangoldt q)]
    _ = 2*Chebyshev.psi (K : ℝ) := by
      rw [psi_natCast_eq_sum_range, sum_Icc_eq_sum_range_shift, mul_sum]
    _ ≤ _ := by nlinarith [psi_bound (K : ℝ) (Nat.cast_nonneg K)]

private theorem coeff_weighted_abs_le (N : ℕ) (w : ℕ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : Antitone w) :
    (∑ i ∈ range N, w i*|coeff N (i+1)|) ≤
      (2*Cpsi)*(∑ i ∈ range N, w i) := by
  have h := DeletionCoefficientTransfer.abs_weighted_sum_le
    (fun q => |coeff N q|) w N hw ha
    (fun K _ => by
      rw [abs_of_nonneg (by
        unfold DeletionCoefficientTransfer.partialSum
        exact sum_nonneg (fun _ _ => abs_nonneg _))]
      exact coeff_partial_abs_le N K)
  rwa [abs_of_nonneg (sum_nonneg (fun i _ => mul_nonneg (hw i) (abs_nonneg _)))] at h

private def reciprocalMass (N : ℕ) : ℝ := ∑ q ∈ Icc 1 N, coeff N q/(q : ℝ)

private theorem reciprocalMass_bound (N : ℕ) :
    |reciprocalMass N| ≤ 2*Cpsi*(1+Real.log (N : ℝ)) := by
  have hC := Cpsi_pos
  have h := coeff_weighted_abs_le N (fun i => 1/((i : ℝ)+1))
    (fun _ => by positivity) (by intro i j hij; dsimp; gcongr)
  have he : (∑ i ∈ range N, 1/((i : ℝ)+1)) = (harmonic N : ℝ) := by
    simp [harmonic, one_div]
  have hsum : |reciprocalMass N| ≤
      ∑ i ∈ range N, 1/((i : ℝ)+1)*|coeff N (i+1)| := by
    rw [reciprocalMass, sum_Icc_eq_sum_range_shift]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro i hi
    simp only [abs_div, Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ)+1)]
    exact le_of_eq (by ring)
  exact hsum.trans (h.trans (by
    rw [he]
    exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)))

private theorem reciprocalMass_limit :
    Tendsto (fun N : ℕ => reciprocalMass N/(N : ℝ)) atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hbound : Tendsto (fun N : ℕ => 2*Cpsi*(1+Real.log (N : ℝ))/(N : ℝ))
      atTop (𝓝 0) := by
    have h := (hconst.add hlog).const_mul (2*Cpsi)
    simp only [add_zero, mul_zero] at h
    apply h.congr'
    filter_upwards with N
    simp only [Function.comp_apply, id_eq]
    ring
  apply squeeze_zero_norm (fun N => ?_) hbound
  simp only [Real.norm_eq_abs, abs_div,
    abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  exact div_le_div_of_nonneg_right (reciprocalMass_bound N) (Nat.cast_nonneg N)

/-- The literal periodic cell mean has a positive linear limit. -/
theorem mean_limit :
    Tendsto (fun N : ℕ => DeletionCellWindow.mean (coeff N) N/(N : ℝ))
      atTop (𝓝 (c2/2)) := by
  have he (N : ℕ) : DeletionCellWindow.mean (coeff N) N =
      ((∑ q ∈ Icc 1 N, coeff N q)-reciprocalMass N)/2 := by
    unfold DeletionCellWindow.mean reciprocalMass
    rw [sum_Icc_eq_sum_range_shift, sum_Icc_eq_sum_range_shift,
      ← sum_sub_distrib, sum_div]
    apply sum_congr rfl
    intro i hi
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have h := (coeff_sum_limit.sub reciprocalMass_limit).div_const 2
  simp only [sub_zero] at h
  convert h using 1
  funext N
  rw [he]
  ring

private theorem moment_bound (N : ℕ) :
    DeletionCellWindow.moment (coeff N) N ≤ 2*Cpsi*(N : ℝ)^(2 : ℕ) := by
  unfold DeletionCellWindow.moment
  calc
    _ ≤ ∑ i ∈ range N, |coeff N (i+1)| * (N : ℝ) := by
      apply sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact_mod_cast (show i+1 ≤ N by have := mem_range.mp hi; omega)
    _ = DeletionCoefficientTransfer.partialSum (fun q => |coeff N q|) N*(N : ℝ) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (coeff_partial_abs_le N N) (Nat.cast_nonneg N)
      nlinarith

private theorem inv_sqrt_sum_bound (N : ℕ) :
    (∑ i ∈ range N, 1/Real.sqrt ((i : ℝ)+1)) ≤ 2*Real.sqrt (N : ℝ) := by
  have hterm (i : ℕ) : 1/Real.sqrt ((i : ℝ)+1) ≤
      2*(Real.sqrt ((i : ℝ)+1)-Real.sqrt (i : ℝ)) := by
    have hp : 0 < Real.sqrt ((i : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
    have h1 := Real.sq_sqrt (show 0 ≤ (i : ℝ)+1 by positivity)
    have h0 := Real.sq_sqrt (show 0 ≤ (i : ℝ) from Nat.cast_nonneg i)
    apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg (Real.sqrt ((i : ℝ)+1)-Real.sqrt (i : ℝ))]
  calc
    _ ≤ ∑ i ∈ range N, 2*(Real.sqrt ((i : ℝ)+1)-Real.sqrt (i : ℝ)) :=
      sum_le_sum (fun i _ => hterm i)
    _ = _ := by
      rw [← mul_sum]
      have h := sum_range_sub (fun n : ℕ => Real.sqrt (n : ℝ)) N
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Real.sqrt_zero,
        sub_zero] using congrArg (fun x : ℝ => 2*x) h

private theorem generator_norm_bound {q : ℕ} (hq : 1 ≤ q) :
    ‖bdGen (1/(q : ℝ))‖ ≤ 2/Real.sqrt (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqR
  have h := DeletionMobiusGram.gram_self_le_two_div hq
  rw [bdGram_self] at h
  have hmul := mul_le_mul_of_nonneg_right h hqR.le
  rw [div_mul_cancel₀ _ hqR.ne'] at hmul
  have hs2 := Real.sq_sqrt hqR.le
  have hprod : ‖bdGen (1/(q : ℝ))‖*Real.sqrt (q : ℝ) ≤ 2 := by
    nlinarith [mul_nonneg (norm_nonneg (bdGen (1/(q : ℝ)))) hs.le,
      sq_nonneg (‖bdGen (1/(q : ℝ))‖*Real.sqrt (q : ℝ))]
  exact (le_div_iff₀ hs).mpr hprod

/-- A square-root upper bound in the original physical norm. -/
theorem norm_forcing_le (N : ℕ) :
    ‖forcing N‖ ≤ 8*(Real.log 4+4)*Real.sqrt (N : ℝ) := by
  have hC := Cpsi_pos
  have hw := coeff_weighted_abs_le N (fun i => 1/Real.sqrt ((i : ℝ)+1))
    (fun _ => by positivity) (by intro i j hij; dsimp; gcongr)
  calc
    ‖forcing N‖ ≤ ∑ i ∈ range N, ‖(coeff N (i+1) : ℂ) • bdGen (1/((i : ℝ)+1))‖ := by
      unfold forcing DeletionCoefficientTransfer.source
      exact norm_sum_le (range N) (fun i =>
        (coeff N (i+1) : ℂ) • bdGen (1/((i : ℝ)+1)))
    _ ≤ 2*(∑ i ∈ range N, 1/Real.sqrt ((i : ℝ)+1)*|coeff N (i+1)|) := by
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have h := mul_le_mul_of_nonneg_left
        (generator_norm_bound (q := i+1) (by omega)) (abs_nonneg (coeff N (i+1)))
      simp only [Nat.cast_add, Nat.cast_one] at h
      convert h using 1
      ring
    _ ≤ 2*((2*Cpsi)*(∑ i ∈ range N, 1/Real.sqrt ((i : ℝ)+1))) := by gcongr
    _ ≤ 2*((2*Cpsi)*(2*Real.sqrt (N : ℝ))) := by
      gcongr
      exact inv_sqrt_sum_bound N
    _ = _ := by unfold Cpsi; ring

/-- The compulsory correction has positive linear physical energy growth. -/
theorem linear_energy_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ N : ℕ in atTop, c*(N : ℝ) ≤ ‖forcing N‖^(2 : ℕ) ∧
      ‖forcing N‖^(2 : ℕ) ≤ C*(N : ℝ) := by
  have hC := Cpsi_pos
  have hc2 : 0 < c2 := lt_of_lt_of_le (by norm_num) c2_lower
  let k : ℝ := c2/4
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k^(3 : ℕ)/(16*Cpsi), 64*Cpsi^(2 : ℕ), by positivity, by positivity, ?_⟩
  have hm := mean_limit.eventually (eventually_gt_nhds (show k < c2/2 by dsimp [k]; linarith))
  filter_upwards [hm, eventually_ge_atTop 1] with N hmean hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmeanlow : k*(N : ℝ) ≤ |DeletionCellWindow.mean (coeff N) N| := by
    have h := (lt_div_iff₀ hNr).mp hmean
    exact le_trans h.le (le_abs_self _)
  have hcube := pow_le_pow_left₀ (mul_nonneg hk.le hNr.le) hmeanlow 3
  have hcoerce := DeletionCellWindow.abs_mean_cube_le_moment_energy (coeff N) N
  have hmom := mul_le_mul_of_nonneg_right (moment_bound N)
    (show 0 ≤ 8*‖forcing N‖^(2 : ℕ) by positivity)
  change _ ≤ 8*DeletionCellWindow.moment (coeff N) N*‖forcing N‖^(2 : ℕ) at hcoerce
  have hcancel : (N : ℝ)^(2 : ℕ)*(k^(3 : ℕ)*(N : ℝ)) ≤
      (N : ℝ)^(2 : ℕ)*(16*Cpsi*‖forcing N‖^(2 : ℕ)) := by nlinarith
  have hlow := le_of_mul_le_mul_left hcancel (sq_pos_of_pos hNr)
  have hnorm := norm_forcing_le N
  change ‖forcing N‖ ≤ 8*Cpsi*Real.sqrt (N : ℝ) at hnorm
  have hsq := mul_self_le_mul_self (norm_nonneg (forcing N)) hnorm
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  constructor
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 16*Cpsi)).mpr (by nlinarith)
  · nlinarith

/-- The literal logarithmically weighted compensated Möbius source. -/
def logSource (N : ℕ) : BDCarrier := DeletionCoefficientTransfer.source
  (fun n => ((moebius n : ℤ) : ℝ)*Real.log (n : ℝ)) N

/-- Prime dilations, with the compensator required by each earlier cutoff. -/
def dilationPackets (N : ℕ) : BDCarrier :=
  ∑ q ∈ Icc 1 N, (vonMangoldt q : ℝ) •
    ((∑ m ∈ Icc 1 (N/q), ((moebius m : ℤ) : ℝ) •
      bdGen (1/((q*m : ℕ) : ℝ))) -
      deningerHarmonicPartial (N/q) • bdGen (1/(q : ℝ)))

private theorem logarithmic_convolution (n : ℕ) :
    ((moebius n : ℤ) : ℝ)*Real.log (n : ℝ) =
      -∑ q ∈ n.divisors, vonMangoldt q*((moebius (n/q) : ℤ) : ℝ) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    GaloisForLFunctions.vonMangoldt_mul_moebius
  simp only [ArithmeticFunction.mul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.neg_apply,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (fun x y =>
    vonMangoldt x*((moebius y : ℤ) : ℝ))] at h
  linarith

private theorem logarithmic_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (N : ℕ) (F : ℕ → E) :
    (∑ n ∈ Icc 1 N, (((moebius n : ℤ) : ℝ)*Real.log (n : ℝ)) • F n) =
      -∑ q ∈ Icc 1 N, (vonMangoldt q : ℝ) •
        ∑ m ∈ Icc 1 (N/q), ((moebius m : ℤ) : ℝ) • F (q*m) := by
  have hswap := Sieve.sum_divisors_swap N (fun q m =>
    (vonMangoldt q*((moebius m : ℤ) : ℝ)) • F (q*m))
  calc
    _ = -∑ n ∈ Icc 1 N, ∑ q ∈ n.divisors,
        (vonMangoldt q*((moebius (n/q) : ℤ) : ℝ)) • F (q*(n/q)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro n hn
      rw [logarithmic_convolution, neg_smul, sum_smul]
      congr 1
      apply sum_congr rfl
      intro q hq
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hq)]
    _ = _ := by rw [hswap]; simp only [smul_sum, smul_smul]

/-- The complete compensated renewal retains its harmonic forcing exactly. -/
theorem compensated_renewal (N : ℕ) :
    logSource N = -dilationPackets N-forcing N := by
  have h := logarithmic_sum N (fun n => bdGen (1/(n : ℝ)))
  have hs : logSource N =
      ∑ n ∈ Icc 1 N, (((moebius n : ℤ) : ℝ)*Real.log (n : ℝ)) •
        bdGen (1/(n : ℝ)) := by
    rw [sum_Icc_eq_sum_range_shift]
    simp [logSource, DeletionCoefficientTransfer.source,
      RCLike.real_smul_eq_coe_smul (K := ℂ), Nat.cast_add, Nat.cast_one]
  have hb : forcing N = ∑ q ∈ Icc 1 N,
      (vonMangoldt q : ℝ) •
        (deningerHarmonicPartial (N/q) • bdGen (1/(q : ℝ))) := by
    rw [sum_Icc_eq_sum_range_shift]
    unfold forcing DeletionCoefficientTransfer.source
    apply sum_congr rfl
    intro i hi
    rw [smul_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [coeff, Nat.cast_add, Nat.cast_one]
    rfl
  rw [hs, h, dilationPackets]
  simp only [smul_sub, sum_sub_distrib]
  rw [← hb]
  abel

end RHTower.DeletionLogPrimeForcing
