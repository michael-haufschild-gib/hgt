import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Logic.Equiv.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Complete damped Ramanujan cubic trace

At a prime with z=p^(-sigma), the reduced-denominator coefficient is
1 on nonnegative valuations, -z/(1-z) at valuation -1, and zero below -1.
These are the prime factors of the normalized coefficients in
`PMPowerDampedMobiusRamanujanWeights`.

We sum the SIGNED multiplicative resonance over every integer valuation pair,
then pass through all finite prime sets. For sigma>1 the complete trace tends
to zeta(sigma)^2; deleting both zero-vector axes gives 1-zeta(sigma)^2.
The full absolute trace also converges, with an explicit Euler product.
No frequencies or signed sectors are discarded in these statements.

This is an arithmetic resonance theorem. Identifying its frequency axes with
literal physical prime diagonals, controlling finite-height near-resonances,
and taking the coupled damping/band limit remain open BAG obligations.
-/

open scoped BigOperators
noncomputable section
namespace RHTower.BAGTrace

def coefficient (z : ℝ) (i : ℤ) : ℝ :=
  if i = -1 then -z / (1-z) else if 0 ≤ i then 1 else 0

def geometric (z : ℝ) (i : ℤ) : ℝ := if 0 ≤ i then z ^ i else 0

def atom (k i : ℤ) : ℝ := if i = k then 1 else 0

def tail (z : ℝ) (i : ℤ) : ℝ := geometric z i - atom 0 i

def localTriple (z : ℝ) (v : ℤ × ℤ) : ℝ :=
  coefficient z v.1 * coefficient z v.2 * coefficient z (v.1+v.2) * z^(v.1+v.2)

theorem geometric_hasSum {z : ℝ} (hz : |z| < 1) :
    HasSum (geometric z) (1-z)⁻¹ := by
  have hp : HasSum (fun n : ℕ => geometric z n) (1-z)⁻¹ := by
    simpa [geometric] using hasSum_geometric_of_abs_lt_one hz
  have hn : HasSum (fun n : ℕ => geometric z (-(n+1))) 0 := by
    convert hasSum_zero (β := ℕ) (α := ℝ) using 1
    funext n
    have h : ¬ (0 : ℤ) ≤ -(n+1) := by omega
    simp only [geometric, if_neg h]
  simpa using hp.of_nat_of_neg_add_one hn

theorem atom_hasSum (k : ℤ) : HasSum (atom k) 1 := by
  exact hasSum_ite_eq k 1

theorem tail_hasSum {z : ℝ} (hz : |z| < 1) :
    HasSum (tail z) ((1-z)⁻¹-1) :=
  (geometric_hasSum hz).sub (atom_hasSum 0)

theorem localTriple_decomposition {z : ℝ} (hz : z ≠ 0) (i j : ℤ) :
    localTriple z (i,j) = geometric z i * geometric z j +
      (z/(1-z)^2)*(atom (-1) i * atom 0 j + atom 0 i * atom (-1) j) -
      (1-z)⁻¹ * (atom (-1) i * tail z j + tail z i * atom (-1) j) := by
  by_cases hi : i < -1
  · have hi0 : ¬ 0 ≤ i := by omega
    have hi1 : i ≠ -1 := by omega
    have hiz : i ≠ 0 := by omega
    simp [localTriple, coefficient, geometric, atom, tail, hi0, hi1, hiz]
  by_cases hj : j < -1
  · have hj0 : ¬ 0 ≤ j := by omega
    have hj1 : j ≠ -1 := by omega
    have hjz : j ≠ 0 := by omega
    simp [localTriple, coefficient, geometric, atom, tail, hj0, hj1, hjz]
  by_cases hi1 : i = -1
  · subst i
    by_cases hj1 : j = -1
    · subst j
      norm_num [localTriple, coefficient, geometric, atom, tail]
    by_cases hjz : j = 0
    · subst j
      simp [localTriple, coefficient, geometric, atom, tail]
      field_simp
    have hj0 : 0 ≤ j := by omega
    have hsum : 0 ≤ -1+j := by omega
    have hsum1 : -1+j ≠ -1 := by omega
    simp [localTriple, coefficient, geometric, atom, tail, hj1, hjz, hj0,
      hsum, hsum1, zpow_add₀ hz]
    field_simp
  have hi0 : 0 ≤ i := by omega
  by_cases hj1 : j = -1
  · subst j
    by_cases hiz : i = 0
    · subst i
      simp [localTriple, coefficient, geometric, atom, tail]
      field_simp
    have hsum : 0 ≤ i + -1 := by omega
    have hsum1 : i + -1 ≠ -1 := by omega
    simp [localTriple, coefficient, geometric, atom, tail, hi1, hiz, hi0,
      hsum, hsum1, zpow_add₀ hz]
    field_simp
  have hj0 : 0 ≤ j := by omega
  have hsum : 0 ≤ i+j := by omega
  have hsum1 : i+j ≠ -1 := by omega
  simp [localTriple, coefficient, geometric, atom, tail, hi1, hj1, hi0, hj0,
    hsum, hsum1, zpow_add₀ hz]

private theorem mul_hasSum {X Y : Type} {f : X → ℝ} {g : Y → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun v : X × Y => f v.1 * g v.2) (a*b) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

theorem localTriple_hasSum {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasSum (localTriple z) ((1-z)⁻¹^2) := by
  have hg := geometric_hasSum (show |z| < 1 by rwa [abs_of_pos hz])
  have ht := tail_hasSum (show |z| < 1 by rwa [abs_of_pos hz])
  have hd := atom_hasSum (-1)
  have h0 := atom_hasSum 0
  have h := ((mul_hasSum hg hg).add
    (((mul_hasSum hd h0).add (mul_hasSum h0 hd)).mul_left (z/(1-z)^2))).sub
    (((mul_hasSum hd ht).add (mul_hasSum ht hd)).mul_left (1-z)⁻¹)
  convert h using 1 <;> try rfl
  · funext v
    exact localTriple_decomposition hz.ne' v.1 v.2
  · have hn : 1-z ≠ 0 := by linarith
    field_simp
    ring

theorem geometric_nonneg {z : ℝ} (hz : 0 ≤ z) (i : ℤ) : 0 ≤ geometric z i := by
  unfold geometric
  split_ifs
  · exact zpow_nonneg hz _
  · exact le_rfl

theorem localTriple_abs {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (i j : ℤ) :
    |localTriple z (i,j)| = geometric z i * geometric z j +
      (z/(1-z)^2)*(atom (-1) i * atom 0 j + atom 0 i * atom (-1) j) +
      (1-z)⁻¹ * (atom (-1) i * tail z j + tail z i * atom (-1) j) := by
  rw [localTriple_decomposition hz.ne']
  have hd : 0 ≤ (1-z)⁻¹ := inv_nonneg.mpr (by linarith)
  have hc : 0 ≤ z/(1-z)^2 := div_nonneg hz.le (sq_nonneg _)
  by_cases hi : i = -1
  · subst i
    by_cases hj : j = 0
    · subst j
      simpa [geometric, tail, atom] using abs_of_nonneg hc
    · simp only [geometric, atom, tail, show ¬ (0 : ℤ) ≤ -1 by omega,
        show (-1 : ℤ) ≠ 0 by omega, hj, if_false, if_true]
      simp only [zero_mul, zero_add, mul_zero, add_zero, one_mul, sub_zero]
      rw [zero_sub, abs_neg]
      exact abs_of_nonneg (mul_nonneg hd (geometric_nonneg hz.le j))
  by_cases hj : j = -1
  · subst j
    by_cases hi0 : i = 0
    · subst i
      simpa [geometric, tail, atom] using abs_of_nonneg hc
    · simp only [geometric, atom, tail, show ¬ (0 : ℤ) ≤ -1 by omega,
        show (-1 : ℤ) ≠ 0 by omega, hi, hi0, if_false, if_true]
      simp only [zero_add, mul_zero, add_zero, mul_one, sub_zero]
      rw [zero_sub, abs_neg]
      exact abs_of_nonneg (mul_nonneg hd (geometric_nonneg hz.le i))
  simp only [atom, hi, hj, if_false, zero_mul, mul_zero, add_zero, sub_zero]
  exact abs_of_nonneg (mul_nonneg (geometric_nonneg hz.le i) (geometric_nonneg hz.le j))

theorem localTriple_abs_hasSum {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasSum (fun v => |localTriple z v|) ((1+4*z)/(1-z)^2) := by
  have hg := geometric_hasSum (show |z| < 1 by rwa [abs_of_pos hz])
  have ht := tail_hasSum (show |z| < 1 by rwa [abs_of_pos hz])
  have hd := atom_hasSum (-1)
  have h0 := atom_hasSum 0
  have h := ((mul_hasSum hg hg).add
    (((mul_hasSum hd h0).add (mul_hasSum h0 hd)).mul_left (z/(1-z)^2))).add
    (((mul_hasSum hd ht).add (mul_hasSum ht hd)).mul_left (1-z)⁻¹)
  convert h using 1 <;> try rfl
  · funext v
    exact localTriple_abs hz hz1 v.1 v.2
  · have hn : 1-z ≠ 0 := by linarith
    field_simp
    ring

private def ProductSummation (X ι : Type) [Fintype ι] : Prop :=
  ∀ (f : ι → X → ℝ) (a : ι → ℝ), (∀ i, HasSum (f i) (a i)) →
    HasSum (fun x : ι → X => ∏ i, f i (x i)) (∏ i, a i)

private theorem productSummation_equiv {X α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (ih : ProductSummation X α) : ProductSummation X β := by
  classical
  intro f a hf
  have h := ih (fun i => f (e i)) (fun i => a (e i)) (fun i => hf (e i))
  rw [e.prod_comp a] at h
  apply (e.arrowCongr (Equiv.refl X)).hasSum_iff.mp
  refine h.congr_fun ?_
  intro x
  exact (Fintype.prod_equiv e _ _ (fun i => by simp [Equiv.arrowCongr])).symm

private theorem productSummation_empty (X : Type) : ProductSummation X PEmpty.{1} := by
  classical
  intro f a hf
  letI : Fintype (PEmpty.{1} → X) := Fintype.ofSubsingleton (fun x => nomatch x)
  simp

private theorem productSummation_option {X α : Type} [Fintype α]
    (ih : ProductSummation X α) : ProductSummation X (Option α) := by
  classical
  intro f a hf
  have hr := ih (fun i => f (some i)) (fun i => a (some i)) (fun i => hf (some i))
  have h : HasSum (fun v : X × (α → X) => f none v.1 * ∏ i, f (some i) (v.2 i))
      (a none * ∏ i, a (some i)) :=
    HasSum.mul (f := f none) (g := fun v : α → X => ∏ i, f (some i) (v i))
      (hf none) hr
      (summable_mul_of_summable_norm (f := f none)
        (g := fun v : α → X => ∏ i, f (some i) (v i))
        (hf none).summable.norm hr.summable.norm)
  have h' : HasSum (fun v : Option α → X => f none (v none) * ∏ i, f (some i) (v (some i)))
      (a none * ∏ i, a (some i)) :=
    ((Equiv.piOptionEquivProd (β := fun _ : Option α => X)).hasSum_iff
      (f := fun v : X × (α → X) => f none v.1 * ∏ i, f (some i) (v.2 i))).mpr h
  simpa only [Fintype.prod_option] using h'

theorem finite_product_hasSum {X : Type} (ι : Type) [Fintype ι]
    (f : ι → X → ℝ) (a : ι → ℝ) (hf : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun x : ι → X => ∏ i, f i (x i)) (∏ i, a i) :=
  Fintype.induction_empty_option (P := ProductSummation X)
    (fun α β _ e h => by
      letI : Fintype α := Fintype.ofEquiv β e.symm
      exact productSummation_equiv e h) (productSummation_empty X)
    (fun _ _ h => productSummation_option h) ι f a hf

def primeWeight (σ : ℝ) (p : Nat.Primes) : ℝ := (p : ℝ)^(-σ)

theorem primeWeight_pos (σ : ℝ) (p : Nat.Primes) : 0 < primeWeight σ p := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast p.property.pos) _

theorem coefficient_primeWeight_neg_one (σ : ℝ) (p : Nat.Primes) :
    coefficient (primeWeight σ p) (-1) = -1/((p : ℝ)^σ-1) := by
  have hp : (p : ℝ)^σ ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast p.property.pos) σ).ne'
  change -((p : ℝ)^(-σ))/(1-(p : ℝ)^(-σ)) = -1/((p : ℝ)^σ-1)
  rw [Real.rpow_neg (by exact_mod_cast p.property.pos.le) σ]
  by_cases h1 : (p : ℝ)^σ = 1
  · simp [h1]
  · field_simp [hp, h1]

theorem primeWeight_le_half {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) :
    primeWeight σ p ≤ 1/2 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p)
    (show -σ ≤ (-1 : ℝ) by linarith)
  rw [Real.rpow_neg_one] at h
  exact h.trans (by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp)

theorem primeWeight_summable {σ : ℝ} (hσ : 1 < σ) : Summable (primeWeight σ) := by
  exact (Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)).subtype _

def trace (σ : ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∑' v : P → ℤ × ℤ, ∏ p : P, localTriple (primeWeight σ p) (v p)

def absoluteTrace (σ : ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∑' v : P → ℤ × ℤ, |∏ p : P, localTriple (primeWeight σ p) (v p)|

theorem trace_eq {σ : ℝ} (hσ : 1 < σ) (P : Finset Nat.Primes) :
    trace σ P = ∏ p ∈ P, (1-primeWeight σ p)⁻¹^2 := by
  have h := finite_product_hasSum P
    (fun p => localTriple (primeWeight σ p))
    (fun p => (1-primeWeight σ p)⁻¹^2)
    (fun p => localTriple_hasSum (primeWeight_pos _ _) (lt_of_le_of_lt
      (primeWeight_le_half hσ _) (by norm_num)))
  exact h.tsum_eq.trans (Finset.prod_coe_sort P (fun p => (1-primeWeight σ p)⁻¹^2))

theorem absoluteTrace_eq {σ : ℝ} (hσ : 1 < σ) (P : Finset Nat.Primes) :
    absoluteTrace σ P = ∏ p ∈ P, (1+4*primeWeight σ p)/(1-primeWeight σ p)^2 := by
  have h := finite_product_hasSum P
    (fun p v => |localTriple (primeWeight σ p) v|)
    (fun p => (1+4*primeWeight σ p)/(1-primeWeight σ p)^2)
    (fun p => localTriple_abs_hasSum (primeWeight_pos _ _) (lt_of_le_of_lt
      (primeWeight_le_half hσ _) (by norm_num)))
  simpa only [absoluteTrace, Finset.abs_prod] using h.tsum_eq.trans
    (Finset.prod_coe_sort P (fun p => (1+4*primeWeight σ p)/(1-primeWeight σ p)^2))

def naturalWeight (σ : ℝ) (hσ : 1 < σ) : ℕ →*₀ ℝ where
  toFun n := (n : ℝ)^(-σ)
  map_zero' := by simpa only [Nat.cast_zero] using Real.zero_rpow (show -σ ≠ 0 by linarith)
  map_one' := by simp
  map_mul' m n := by simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

theorem primeWeight_euler {σ : ℝ} (hσ : 1 < σ) :
    HasProd (fun p => (1-primeWeight σ p)⁻¹) (∑' n : ℕ, (n : ℝ)^(-σ)) := by
  have hsum : Summable (fun n => ‖naturalWeight σ hσ n‖) :=
    (Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)).norm
  exact EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum

theorem complete_signed_trace_limit {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto (trace σ) Filter.atTop (nhds ((∑' n : ℕ, (n : ℝ)^(-σ))^2)) := by
  have h := (primeWeight_euler hσ).mul (primeWeight_euler hσ)
  change Filter.Tendsto (fun P => trace σ P) _ _
  simpa only [HasProd, SummationFilter.unconditional, trace_eq hσ, pow_two] using h

theorem localAxis_hasSum {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasSum (fun i : ℤ => localTriple z (i,0)) ((1-z)⁻¹^2) := by
  have h := (geometric_hasSum (show |z| < 1 by rwa [abs_of_pos hz])).add
    ((atom_hasSum (-1)).mul_left (z/(1-z)^2))
  convert h using 1 <;> try rfl
  · funext i
    rw [localTriple_decomposition hz.ne']
    simp [geometric, tail, atom]
  · have hn : 1-z ≠ 0 := by linarith
    field_simp
    ring

def axisTrace (σ : ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∑' v : P → ℤ, ∏ p : P, localTriple (primeWeight σ p) (v p,0)

theorem axisTrace_eq {σ : ℝ} (hσ : 1 < σ) (P : Finset Nat.Primes) :
    axisTrace σ P = trace σ P := by
  have h := finite_product_hasSum P
    (fun p i => localTriple (primeWeight σ p) (i,0))
    (fun p => (1-primeWeight σ p)⁻¹^2)
    (fun p => localAxis_hasSum (primeWeight_pos _ _) (lt_of_le_of_lt
      (primeWeight_le_half hσ _) (by norm_num)))
  rw [trace_eq hσ]
  exact h.tsum_eq.trans (Finset.prod_coe_sort P (fun p => (1-primeWeight σ p)⁻¹^2))

/-- Remove both arithmetic frequency axes and restore their common origin.
This definition does not assert their identification with discrete prime diagonals. -/
def connectedTrace (σ : ℝ) (P : Finset Nat.Primes) : ℝ :=
  trace σ P - axisTrace σ P - axisTrace σ P + 1

theorem connectedTrace_eq {σ : ℝ} (hσ : 1 < σ) (P : Finset Nat.Primes) :
    connectedTrace σ P = 1 - trace σ P := by
  rw [connectedTrace, axisTrace_eq hσ]
  ring

theorem complete_connected_trace_limit {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto (connectedTrace σ) Filter.atTop
      (nhds (1-(∑' n : ℕ, (n : ℝ)^(-σ))^2)) := by
  change Filter.Tendsto (fun P => connectedTrace σ P) _ _
  simp_rw [connectedTrace_eq hσ]
  exact (tendsto_const_nhds : Filter.Tendsto
    (fun _ : Finset Nat.Primes => (1 : ℝ)) Filter.atTop (nhds 1)).sub
      (complete_signed_trace_limit hσ)

theorem zetaSeries_eq {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ)^(-σ)) = (riemannZeta (σ : ℂ)).re := by
  have h : (↑(∑' n : ℕ, (n : ℝ)^(-σ)) : ℂ) = riemannZeta (σ : ℂ) := by
    rw [Complex.ofReal_tsum, zeta_eq_tsum_one_div_nat_cpow (by simpa using hσ)]
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp only [Complex.ofReal_neg, Complex.ofReal_natCast, Complex.cpow_neg, one_div]
  exact congrArg Complex.re h

theorem complete_signed_trace_zeta {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto (trace σ) Filter.atTop (nhds ((riemannZeta (σ : ℂ)).re^2)) := by
  simpa only [zetaSeries_eq hσ] using complete_signed_trace_limit hσ

theorem complete_connected_trace_zeta {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto (connectedTrace σ) Filter.atTop (nhds (1-(riemannZeta (σ : ℂ)).re^2)) := by
  simpa only [zetaSeries_eq hσ] using complete_connected_trace_limit hσ

theorem complete_absolute_trace_limit {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto (absoluteTrace σ) Filter.atTop
      (nhds ((riemannZeta (σ : ℂ)).re^2 * ∏' p, (1+4*primeWeight σ p))) := by
  have hplus := Real.multipliable_one_add_of_summable ((primeWeight_summable hσ).mul_left 4)
  have h := ((primeWeight_euler hσ).mul (primeWeight_euler hσ)).mul hplus.hasProd
  have hp : HasProd (fun p => (1+4*primeWeight σ p)/(1-primeWeight σ p)^2)
      ((∑' n : ℕ, (n : ℝ)^(-σ))^2 * ∏' p, (1+4*primeWeight σ p)) := by
    simp only [pow_two]
    refine h.congr_fun fun p => ?_
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [zetaSeries_eq hσ] at hp
  change Filter.Tendsto (fun P => absoluteTrace σ P) _ _
  simpa only [HasProd, SummationFilter.unconditional, absoluteTrace_eq hσ,
    zetaSeries_eq hσ] using hp

private theorem remove_axes_hasSum {X : Type} [Zero X] [DecidableEq X]
    {f : X × X → ℝ} {A B C : ℝ} (h : HasSum f A)
    (hl : HasSum (fun x => f (0,x)) B) (hr : HasSum (fun x => f (x,0)) C) :
    HasSum (fun v => if v.1 = 0 ∨ v.2 = 0 then 0 else f v) (A-B-C+f (0,0)) := by
  have hd := hasSum_ite_eq (0 : X) (1 : ℝ)
  have hleft := mul_hasSum hd hl
  have hright := mul_hasSum hr hd
  have horigin := (mul_hasSum hd hd).mul_left (f (0,0))
  have h' := ((h.sub hleft).sub hright).add horigin
  simp only [one_mul, mul_one] at h'
  refine h'.congr_fun ?_
  intro v
  rcases v with ⟨x,y⟩
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx,hy]

def offAxesTrace (σ : ℝ) (P : Finset Nat.Primes) : ℝ := by
  classical
  exact ∑' v : (P → ℤ) × (P → ℤ),
    if v.1 = 0 ∨ v.2 = 0 then 0
    else ∏ p : P, localTriple (primeWeight σ p) (v.1 p,v.2 p)

theorem offAxesTrace_eq {σ : ℝ} (hσ : 1 < σ) (P : Finset Nat.Primes) :
    offAxesTrace σ P = connectedTrace σ P := by
  classical
  let f : (P → ℤ) × (P → ℤ) → ℝ :=
    fun v => ∏ p : P, localTriple (primeWeight σ p) (v.1 p,v.2 p)
  have hfinit := finite_product_hasSum P
    (fun p => localTriple (primeWeight σ p))
    (fun p => (1-primeWeight σ p)⁻¹^2)
    (fun p => localTriple_hasSum (primeWeight_pos _ _) (lt_of_le_of_lt
      (primeWeight_le_half hσ _) (by norm_num)))
  have hf : HasSum f (trace σ P) :=
    ((Equiv.arrowProdEquivProdArrow P (fun _ => ℤ) (fun _ => ℤ)).hasSum_iff
      (f := f)).mp hfinit.summable.hasSum
  have har := finite_product_hasSum P
    (fun p i => localTriple (primeWeight σ p) (i,0))
    (fun p => (1-primeWeight σ p)⁻¹^2)
    (fun p => localAxis_hasSum (primeWeight_pos _ _) (lt_of_le_of_lt
      (primeWeight_le_half hσ _) (by norm_num)))
  have hr : HasSum (fun x => f (x,0)) (axisTrace σ P) := har.summable.hasSum
  have hl : HasSum (fun x => f (0,x)) (axisTrace σ P) := by
    refine hr.congr_fun fun x => ?_
    apply Finset.prod_congr rfl
    intro p hp
    simp [localTriple, mul_comm]
  have h00 : f (0,0) = 1 := by simp [f, localTriple, coefficient]
  have hmask := remove_axes_hasSum hf hl hr
  rw [h00] at hmask
  exact hmask.tsum_eq

theorem complete_offAxes_trace_zeta {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto (offAxesTrace σ) Filter.atTop
      (nhds (1-(riemannZeta (σ : ℂ)).re^2)) := by
  simpa only [show offAxesTrace σ = connectedTrace σ from
    funext (offAxesTrace_eq hσ)] using complete_connected_trace_zeta hσ

end RHTower.BAGTrace
