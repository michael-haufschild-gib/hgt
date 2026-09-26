import GaloisForLFunctions.RHTower.MonotoneSourceGramContraction
import GaloisForLFunctions.RHTower.ThetaRawGramGrowthObstruction
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The complete theta Gram form is not a finite-order local differential energy

Let B be the sign-adjusted cleared logarithmic-moment matrix and put
A(i,j)=(2i+1)!(2j+1)! B(i,j). The actual normalized theta moments m satisfy
A(0,n)=m(n+1), whereas A(i,n-i)/m(n+1) tends to zero for every fixed i>0.
The proof keeps the whole source and uses its divergent consecutive moment ratios.

A local derivative pairing of any fixed finite order gives anti-diagonals of A
that are polynomials of uniformly bounded degree. Lagrange interpolation excludes
such a realization. The theorem allows arbitrary signed cross-moment data, so
neither positivity nor boundedness of the putative coefficient weights is needed.
Weighted odd-monomial Gram representations are excluded as a special case.

The positive survivor is the exact normalized anti-diagonal limit. Nonlocal
operators, unbounded derivative order, and other degree-dependent feature maps
remain open. This is a source representation obstruction, not an RH conclusion
or a prohibition on every integration-by-parts argument.
-/

open Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower.LocalGram
open MonotoneSourceGram


/-- The entire first row fixes every positive moment of any putative local weight. -/
theorem cleared_zero_row (m : ℕ → ℝ) (hm : m 0 = 1) (j : ℕ) :
    cleared m 0 j = m (j+1) / ((2*j+1).factorial : ℝ) := by
  simp only [cleared, min_eq_left (Nat.zero_le j), zero_add, Finset.sum_range_one,
    Nat.mul_zero, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, mul_one, hm]
  have he : ((2*(j+1)).factorial : ℝ) =
      (2*(j+1)) * ((2*j+1).factorial : ℝ) := by
    rw [show 2*(j+1) = (2*j+1)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [he]
  have hj : (j+1:ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- Consecutive inverse moment ratios vanish at every fixed separation. -/
theorem separated_ratio_tendsto_zero {m : ℕ → ℝ}
    (hm : ∀ n, 0 < m n)
    (hr : Tendsto (fun n => m (n+1) / m n) atTop atTop)
    (k : ℕ) :
    Tendsto (fun n => m n / m (n+k+1)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n => m n / m (n+1)) atTop (𝓝 0) := by
    refine hr.inv_tendsto_atTop.congr (fun n => ?_)
    change (m (n+1) / m n)⁻¹ = m n / m (n+1)
    exact inv_div _ _
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have hh := ih.mul (hbase.comp (tendsto_add_atTop_nat (k+1)))
    simp only [zero_mul, Function.comp_def] at hh
    refine hh.congr (fun n => ?_)
    have hz : m (n+(k+1)) ≠ 0 := (hm _).ne'
    rw [show n+k+1 = n+(k+1) by omega]
    field_simp

/-- Factor multiplying a pair of moments after removing the odd factorials. -/
def coefficient (i j k : ℕ) : ℝ :=
  2 * (i+j+1-2*k : ℕ) * ((2*i+1).factorial : ℝ) * (2*j+1).factorial /
    (((2*(i+j+1-k)).factorial : ℝ) * (2*k).factorial)

theorem coefficient_nonneg (i j k : ℕ) : 0 ≤ coefficient i j k := by
  unfold coefficient
  positivity

theorem coefficient_le {i j k : ℕ} (hki : k ≤ i) :
    coefficient i j k ≤ ((2*i+1).factorial : ℝ) := by
  let N := i+j+1-k
  have hn : 0 < N := by dsimp [N]; omega
  have hl : i+j+1-2*k ≤ N := by dsimp [N]; omega
  have hj : 2*j+1 ≤ 2*N-1 := by dsimp [N]; omega
  have hnat : 2*(i+j+1-2*k)*(2*j+1).factorial ≤ (2*N).factorial := by
    rw [← Nat.mul_factorial_pred (show 2*N ≠ 0 by omega)]
    exact Nat.mul_le_mul (by omega) (Nat.factorial_le hj)
  have hreal : 2*(i+j+1-2*k : ℕ)*( (2*j+1).factorial : ℝ) ≤
      ((2*N).factorial : ℝ) := by exact_mod_cast hnat
  have hk : (1:ℝ) ≤ (2*k).factorial := by exact_mod_cast Nat.factorial_pos (2*k)
  have hd : 0 < ((2*N).factorial : ℝ) * (2*k).factorial := by positivity
  unfold coefficient
  change _ / (((2*N).factorial : ℝ) * (2*k).factorial) ≤ _
  apply (div_le_iff₀ hd).2
  calc
    _ = ((2*i+1).factorial : ℝ) * (2*(i+j+1-2*k : ℕ)*( (2*j+1).factorial : ℝ)) := by ring
    _ ≤ ((2*i+1).factorial : ℝ) * ((2*N).factorial : ℝ) := by gcongr
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      nlinarith [show (0:ℝ) ≤ (2*N).factorial by positivity]

theorem coefficient_zero_le {i : ℕ} (hi : 0 < i) (j : ℕ) :
    coefficient i j 0 ≤ ((2*i+1).factorial : ℝ) / (j+1) := by
  have hnat : (j+1)*(2*j+1).factorial ≤ (2*(i+j+1)-1).factorial := by
    calc
      _ ≤ (2*j+2)*(2*j+1).factorial := Nat.mul_le_mul_right _ (by omega)
      _ = (2*j+2).factorial := by
        convert (Nat.factorial_succ (2*j+1)).symm using 1
      _ ≤ _ := Nat.factorial_le (by omega)
  have hnat2 : (2*(i+j+1))*((j+1)*(2*j+1).factorial) ≤
      (2*(i+j+1)).factorial := by
    rw [← Nat.mul_factorial_pred (show 2*(i+j+1) ≠ 0 by omega)]
    exact Nat.mul_le_mul_left _ hnat
  have hreal : 2*(i+j+1:ℕ)*((j+1:ℝ)*((2*j+1).factorial : ℝ)) ≤
      ((2*(i+j+1)).factorial : ℝ) := by exact_mod_cast hnat2
  have hd : (0:ℝ) < (2*(i+j+1)).factorial := by positivity
  have hj : (0:ℝ) < j+1 := by positivity
  unfold coefficient
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
  apply (le_div_iff₀ hj).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).2
  calc
    _ = ((2*i+1).factorial : ℝ) * (2*(i+j+1:ℕ)*((j+1:ℝ)*((2*j+1).factorial : ℝ))) := by ring
    _ ≤ _ := by gcongr

/-- The factorial-rescaled cleared matrix. -/
def rescaled (m : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ((2*i+1).factorial : ℝ) * (2*j+1).factorial * cleared m i j

theorem rescaled_zero (m : ℕ → ℝ) (hm : m 0 = 1) (j : ℕ) :
    rescaled m 0 j = m (j+1) := by
  rw [rescaled, cleared_zero_row m hm]
  simp only [Nat.mul_zero, zero_add, Nat.factorial_one, Nat.cast_one, one_mul]
  have h : ((2*j+1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem rescaled_eq_sum {m : ℕ → ℝ} {i j : ℕ} (hij : i ≤ j) :
    rescaled m i j = ∑ k ∈ Finset.range (i+1),
      coefficient i j k * m (i+j+1-k) * m k := by
  unfold rescaled cleared
  rw [min_eq_left hij]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold coefficient
  ring

theorem coefficient_zero_tendsto {i : ℕ} (hi : 0 < i) :
    Tendsto (fun j => coefficient i j 0) atTop (𝓝 0) := by
  have hn : Tendsto (fun j : ℕ => ((j+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hu : Tendsto (fun j : ℕ => ((2*i+1).factorial : ℝ) / (j+1)) atTop (𝓝 0) := by
    have hh := hn.inv_tendsto_atTop.const_mul ((2*i+1).factorial : ℝ)
    convert hh using 1 <;> simp [div_eq_mul_inv, Pi.inv_apply]
  exact squeeze_zero (fun j => coefficient_nonneg i j 0) (coefficient_zero_le hi) hu

theorem shifted_ratio_tendsto_zero {m : ℕ → ℝ}
    (hm : ∀ n, 0 < m n)
    (hr : Tendsto (fun n => m (n+1) / m n) atTop atTop)
    {i k : ℕ} (hk0 : 0 < k) (hki : k ≤ i) :
    Tendsto (fun j => m (i+j+1-k) / m (i+j+1)) atTop (𝓝 0) := by
  have h := (separated_ratio_tendsto_zero hm hr (k-1)).comp
    (tendsto_add_atTop_nat (i+1-k))
  refine h.congr (fun j => ?_)
  simp only [Function.comp_def]
  congr 1 <;> congr 1 <;> omega

/-- Every fixed positive row disappears relative to its zeroth-row moment. -/
theorem rescaled_row_tendsto_zero {m : ℕ → ℝ}
    (hm : ∀ n, 0 < m n)
    (hr : Tendsto (fun n => m (n+1) / m n) atTop atTop)
    {i : ℕ} (hi : 0 < i) :
    Tendsto (fun j => rescaled m i j / m (i+j+1)) atTop (𝓝 0) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (i+1)) :
      Tendsto (fun j => coefficient i j k * (m (i+j+1-k) / m (i+j+1)) * m k)
        atTop (𝓝 0) := by
    have hki : k ≤ i := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    by_cases hk0 : k = 0
    · subst k
      have h := (coefficient_zero_tendsto hi).mul (tendsto_const_nhds (x := m 0))
      simp only [zero_mul] at h
      refine h.congr (fun j => ?_)
      simp only [Nat.sub_zero, div_self (hm _).ne', mul_one]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hu := ((shifted_ratio_tendsto_zero hm hr hkpos hki).const_mul
        ((2*i+1).factorial : ℝ)).mul (tendsto_const_nhds (x := m k))
      simp only [mul_zero, zero_mul] at hu
      apply squeeze_zero (fun j => mul_nonneg
        (mul_nonneg (coefficient_nonneg i j k) (div_nonneg (hm _).le (hm _).le))
        (hm k).le) (fun j => ?_) hu
      apply mul_le_mul_of_nonneg_right _ (hm k).le
      exact mul_le_mul_of_nonneg_right (coefficient_le hki)
        (div_nonneg (hm _).le (hm _).le)
  have hsum := tendsto_finsetSum (Finset.range (i+1)) hterm
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop i] with j hj
  rw [rescaled_eq_sum hj, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Fixed interpolation coefficients recover a bounded-degree polynomial at zero. -/
def interpolationWeight (d i : ℕ) : ℝ :=
  (Lagrange.basis (Finset.range (d+1)) (fun j : ℕ => (j : ℝ)+1) i).eval 0

theorem polynomial_zero_from_positive_nodes {d : ℕ} (p : Polynomial ℝ)
    (hp : p.natDegree ≤ d) :
    p.eval 0 = ∑ i ∈ Finset.range (d+1), p.eval ((i : ℝ)+1) * interpolationWeight d i := by
  have hinj : Set.InjOn (fun j : ℕ => (j : ℝ)+1) (Finset.range (d+1)) := by
    intro a ha b hb hab
    have he : (a:ℝ) = (b:ℝ) := by linarith
    exact_mod_cast he
  have hdeg : p.degree < ((Finset.range (d+1)).card : WithBot ℕ) := by
    simp only [Finset.card_range]
    exact lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
  have h := congrArg (Polynomial.eval (0:ℝ)) (Lagrange.eq_interpolate hinj hdeg)
  simpa [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, interpolationWeight] using h

/-- Bounded-degree anti-diagonals cannot develop a spike at the zeroth row. -/
theorem not_polynomial_spike (d : ℕ) (p : ℕ → Polynomial ℝ) (r : ℕ → ℝ)
    (hp : ∀ n, (p n).natDegree ≤ d)
    (hzero : Tendsto (fun n => (p n).eval 0 / r n) atTop (𝓝 1))
    (hpos : ∀ i : ℕ, 0 < i → Tendsto (fun n => (p n).eval (i : ℝ) / r n) atTop (𝓝 0)) :
    False := by
  have hh := tendsto_finsetSum (Finset.range (d+1)) (fun i hi =>
    (hpos (i+1) (by omega)).mul_const (interpolationWeight d i))
  simp only [zero_mul, Finset.sum_const_zero] at hh
  have hh' : Tendsto (fun n => (p n).eval 0 / r n) atTop (𝓝 0) := by
    refine hh.congr (fun n => ?_)
    rw [polynomial_zero_from_positive_nodes (p n) (hp n), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  have h := tendsto_nhds_unique hzero hh'
  norm_num at h

theorem normalized_moment_positive (n : ℕ) : 0 < thetaCuspNormalizedEvenMoment n :=
  div_pos (thetaCuspRawEvenMoment_pos n) (thetaCuspRawEvenMoment_pos 0)

theorem normalized_moment_zero : thetaCuspNormalizedEvenMoment 0 = 1 := by
  simp [thetaCuspNormalizedEvenMoment, (thetaCuspRawEvenMoment_pos 0).ne']

theorem normalized_moment_ratio_atTop :
    Tendsto (fun n => thetaCuspNormalizedEvenMoment (n+1) /
      thetaCuspNormalizedEvenMoment n) atTop atTop := by
  refine tendsto_thetaCuspRawEvenMoment_ratio_atTop.congr (fun n => ?_)
  unfold thetaCuspNormalizedEvenMoment
  have h0 := (thetaCuspRawEvenMoment_pos 0).ne'
  field_simp

/-- The complete theta matrix has a normalized anti-diagonal spike. -/
theorem theta_antidiagonal_limit (i : ℕ) :
    Tendsto (fun n => rescaled thetaCuspNormalizedEvenMoment i (n-i) /
      thetaCuspNormalizedEvenMoment (n+1)) atTop (𝓝 (if i = 0 then 1 else 0)) := by
  by_cases hi : i = 0
  · subst i
    simp [rescaled_zero _ normalized_moment_zero,
      div_self (normalized_moment_positive _).ne']
  · rw [if_neg hi]
    have h := (rescaled_row_tendsto_zero normalized_moment_positive
      normalized_moment_ratio_atTop (Nat.pos_of_ne_zero hi)).comp (tendsto_sub_atTop_nat i)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop i] with n hn
    simp only [Function.comp_def]
    rw [show i+(n-i)+1 = n+1 by omega]

/-- No uniformly bounded polynomial degree can realize the rescaled anti-diagonals. -/
theorem theta_no_bounded_degree_antidiagonals :
    ¬ ∃ d : ℕ, ∃ p : ℕ → Polynomial ℝ, (∀ n, (p n).natDegree ≤ d) ∧
      ∀ n i : ℕ, i ≤ n → (p n).eval (i : ℝ) =
        rescaled thetaCuspNormalizedEvenMoment i (n-i) := by
  rintro ⟨d,p,hp,he⟩
  apply not_polynomial_spike d p (fun n => thetaCuspNormalizedEvenMoment (n+1)) hp
  · have h : Tendsto (fun n => rescaled thetaCuspNormalizedEvenMoment 0 (n-0) /
        thetaCuspNormalizedEvenMoment (n+1)) atTop (𝓝 1) := by
      simpa using theta_antidiagonal_limit 0
    refine h.congr (fun n => ?_)
    have he0 := he n 0 (Nat.zero_le n)
    simp only [Nat.cast_zero] at he0
    rw [he0]
  · intro i hi
    have h := theta_antidiagonal_limit i
    rw [if_neg (Nat.ne_of_gt hi)] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop i] with n hn
    rw [he n i hn]

theorem rescaled_raw (m : ℕ → ℝ) (i j : ℕ) :
    ((2*i+1).factorial : ℝ) * (2*j+1).factorial * raw m i j = m (i+j+1) := by
  have hi : ((2*i+1).factorial : ℝ) ≠ 0 := by positivity
  have hj : ((2*j+1).factorial : ℝ) ≠ 0 := by positivity
  unfold raw
  field_simp

/-- Even arbitrary signed moment weights cannot give a local odd-monomial Gram realization. -/
theorem theta_no_weighted_moment_gram :
    ¬ ∃ m : ℕ → ℝ, ∀ i j, raw m i j = cleared thetaCuspNormalizedEvenMoment i j := by
  rintro ⟨m,hm⟩
  apply theta_no_bounded_degree_antidiagonals
  refine ⟨0, fun n => Polynomial.C (m (n+1)), fun n => by simp, ?_⟩
  intro n i hi
  simp only [Polynomial.eval_C]
  rw [rescaled, ← hm, rescaled_raw, show i+(n-i)+1 = n+1 by omega]

open Polynomial

/-- Arbitrary moment data for all local cross-derivatives up to a fixed order. -/
def localJetMatrix (r : ℕ) (w : ℕ → ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (r+1), ∑ b ∈ Finset.range (r+1),
    ((2*i+1).descFactorial a : ℝ) * (2*j+1).descFactorial b * w a b (i+j)

def jetPairPolynomial (n a b : ℕ) : Polynomial ℝ :=
  (descPochhammer ℝ a).comp (C 2 * X + 1) *
    (descPochhammer ℝ b).comp (C (2*(n:ℝ)+1) - C 2 * X)

theorem jetPairPolynomial_degree (n a b : ℕ) :
    (jetPairPolynomial n a b).natDegree ≤ a+b := by
  have hL : (C 2 * X + 1 : Polynomial ℝ).natDegree ≤ 1 := by compute_degree
  have hR : (C (2*(n:ℝ)+1) - C 2 * X : Polynomial ℝ).natDegree ≤ 1 := by compute_degree
  apply Polynomial.natDegree_mul_le_of_le
  · exact Polynomial.natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left a hL)
  · exact Polynomial.natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left b hR)

theorem jetPairPolynomial_eval {n i : ℕ} (hi : i ≤ n) (a b : ℕ) :
    (jetPairPolynomial n a b).eval (i:ℝ) =
      ((2*i+1).descFactorial a : ℝ) * (2*(n-i)+1).descFactorial b := by
  simp only [jetPairPolynomial, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_sub]
  have hl : 2*(i:ℝ)+1 = ((2*i+1 : ℕ):ℝ) := by push_cast; ring
  have hr : 2*(n:ℝ)+1-2*(i:ℝ) = ((2*(n-i)+1 : ℕ):ℝ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hi]
    norm_num
    ring
  rw [hl,hr,descPochhammer_eval_eq_descFactorial,descPochhammer_eval_eq_descFactorial]

def localJetPolynomial (r : ℕ) (w : ℕ → ℕ → ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ a ∈ Finset.range (r+1), ∑ b ∈ Finset.range (r+1),
    C (w a b n) * jetPairPolynomial n a b

theorem localJetPolynomial_degree (r : ℕ) (w : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (localJetPolynomial r w n).natDegree ≤ 2*r := by
  unfold localJetPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro b hb
  have hab : a+b ≤ 2*r := by
    simp only [Finset.mem_range] at ha hb
    omega
  exact (Polynomial.natDegree_C_mul_le _ _).trans ((jetPairPolynomial_degree n a b).trans hab)

theorem localJetPolynomial_eval (r : ℕ) (w : ℕ → ℕ → ℕ → ℝ)
    {n i : ℕ} (hi : i ≤ n) :
    (localJetPolynomial r w n).eval (i:ℝ) = localJetMatrix r w i (n-i) := by
  unfold localJetPolynomial localJetMatrix
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    jetPairPolynomial_eval hi, show i+(n-i)=n by omega]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- No fixed finite local differential order, even with arbitrary signed cross-moments,
can realize the complete theta matrix in the factorial-normalized odd monomial basis. -/
theorem theta_no_finite_local_jet_gram :
    ¬ ∃ r : ℕ, ∃ w : ℕ → ℕ → ℕ → ℝ, ∀ i j : ℕ,
      rescaled thetaCuspNormalizedEvenMoment i j = localJetMatrix r w i j := by
  rintro ⟨r,w,hw⟩
  apply theta_no_bounded_degree_antidiagonals
  refine ⟨2*r, localJetPolynomial r w, localJetPolynomial_degree r w, ?_⟩
  intro n i hi
  rw [localJetPolynomial_eval r w hi, hw]

end RHTower.LocalGram
