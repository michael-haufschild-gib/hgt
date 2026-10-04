import GaloisForLFunctions.HTGeometry.SchwartzSpectralQuadraticSeparation

/-!
# Polynomially weighted jet limits on fixed Schwartz tests

Uniform errors that vanish after a fixed polynomial weight are stable under
finite sums and products. The exact scalar ODE and Leibniz recurrence propagate
such limits from a phase coefficient and its zeroth solution value to every
solution derivative. Acting on any fixed Schwartz test converts these weighted
jet limits into convergence in the full Schwartz topology.

These analytic theorems are used for the original Gamma clock cutoffs. Their
source hypotheses must be discharged for those cutoffs; the generic statements
alone do not prove the TG operator limit or RH.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped SchwartzMap
namespace RHTower

/-- Uniform polynomial control of a limit and a vanishing polynomially weighted error. -/
def PolynomiallyWeightedLimit {ι : Type*} (l : Filter ι)
    (F : ι → ℝ → ℂ) (f : ℝ → ℂ) : Prop :=
  ∃ (k : ℕ) (C : ℝ) (e : ι → ℝ), 0 ≤ C ∧ (∀ i, 0 ≤ e i) ∧
    Tendsto e l (𝓝 0) ∧ (∀ t, ‖f t‖ ≤ C*(1+‖t‖)^k) ∧
      ∀ᶠ i in l, ∀ t, ‖F i t-f t‖ ≤ e i*(1+‖t‖)^k

namespace PolynomiallyWeightedLimit
variable {ι : Type*} {l : Filter ι} {F G : ι → ℝ → ℂ} {f g : ℝ → ℂ}

/-- Constant scalar families have zero weighted error. -/
theorem const (c : ℂ) : PolynomiallyWeightedLimit l (fun _ _ => c) (fun _ => c) := by
  refine ⟨0, ‖c‖, fun _ => 0, norm_nonneg _, fun _ => le_rfl, tendsto_const_nhds, ?_, ?_⟩
  · simp
  · simp

private theorem weight_le_add (t : ℝ) (k m : ℕ) :
    (1+‖t‖)^k ≤ (1+‖t‖)^(k+m) :=
  pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.le_add_right k m)

/-- Addition preserves the same global form of convergence. -/
theorem add (hF : PolynomiallyWeightedLimit l F f) (hG : PolynomiallyWeightedLimit l G g) :
    PolynomiallyWeightedLimit l (fun i t => F i t+G i t) (fun t => f t+g t) := by
  obtain ⟨k, C, e, hC, he, ht, hf, hFe⟩ := hF
  obtain ⟨m, D, d, hD, hd, hu, hg, hGe⟩ := hG
  refine ⟨k+m, C+D, fun i => e i+d i, add_nonneg hC hD,
    fun i => add_nonneg (he i) (hd i), ?_, ?_, ?_⟩
  · simpa only [add_zero] using ht.add hu
  · intro t
    have hk := weight_le_add t k m
    have hm : (1+‖t‖)^m ≤ (1+‖t‖)^(k+m) := by
      simpa only [Nat.add_comm] using weight_le_add t m k
    calc
      _ ≤ ‖f t‖+‖g t‖ := norm_add_le _ _
      _ ≤ C*(1+‖t‖)^k+D*(1+‖t‖)^m := add_le_add (hf t) (hg t)
      _ ≤ (C+D)*(1+‖t‖)^(k+m) := by
        nlinarith [mul_le_mul_of_nonneg_left hk hC, mul_le_mul_of_nonneg_left hm hD]
  · filter_upwards [hFe, hGe] with i hFi hGi
    intro t
    have hk := weight_le_add t k m
    have hm : (1+‖t‖)^m ≤ (1+‖t‖)^(k+m) := by
      simpa only [Nat.add_comm] using weight_le_add t m k
    calc
      _ = ‖(F i t-f t)+(G i t-g t)‖ := by congr 1; ring
      _ ≤ ‖F i t-f t‖+‖G i t-g t‖ := norm_add_le _ _
      _ ≤ e i*(1+‖t‖)^k+d i*(1+‖t‖)^m := add_le_add (hFi t) (hGi t)
      _ ≤ (e i+d i)*(1+‖t‖)^(k+m) := by
        nlinarith [mul_le_mul_of_nonneg_left hk (he i), mul_le_mul_of_nonneg_left hm (hd i)]

/-- Products preserve weighted convergence without an operator-norm hypothesis. -/
theorem mul (hF : PolynomiallyWeightedLimit l F f) (hG : PolynomiallyWeightedLimit l G g) :
    PolynomiallyWeightedLimit l (fun i t => F i t*G i t) (fun t => f t*g t) := by
  obtain ⟨k, C, e, hC, he, ht, hf, hFe⟩ := hF
  obtain ⟨m, D, d, hD, hd, hu, hg, hGe⟩ := hG
  refine ⟨k+m, C*D, fun i => e i*d i+e i*D+C*d i, mul_nonneg hC hD,
    fun i => add_nonneg (add_nonneg (mul_nonneg (he i) (hd i)) (mul_nonneg (he i) hD))
      (mul_nonneg hC (hd i)), ?_, ?_, ?_⟩
  · simpa only [mul_zero, zero_mul, add_zero] using
      ((ht.mul hu).add (ht.mul_const D)).add (hu.const_mul C)
  · intro t
    calc
      _ = ‖f t‖*‖g t‖ := norm_mul _ _
      _ ≤ (C*(1+‖t‖)^k)*(D*(1+‖t‖)^m) :=
        mul_le_mul (hf t) (hg t) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  · filter_upwards [hFe, hGe] with i hFi hGi
    intro t
    calc
      _ = ‖(F i t-f t)*(G i t-g t)+(F i t-f t)*g t+f t*(G i t-g t)‖ := by
        congr 1; ring
      _ ≤ ‖F i t-f t‖*‖G i t-g t‖+‖F i t-f t‖*‖g t‖+‖f t‖*‖G i t-g t‖ := by
        calc
          _ ≤ ‖(F i t-f t)*(G i t-g t)+(F i t-f t)*g t‖+‖f t*(G i t-g t)‖ := norm_add_le _ _
          _ ≤ _ := by
            simpa only [norm_mul] using
              add_le_add (norm_add_le ((F i t-f t)*(G i t-g t)) ((F i t-f t)*g t))
                (le_refl ‖f t*(G i t-g t)‖)
      _ ≤ (e i*(1+‖t‖)^k)*(d i*(1+‖t‖)^m)+
          (e i*(1+‖t‖)^k)*(D*(1+‖t‖)^m)+
          (C*(1+‖t‖)^k)*(d i*(1+‖t‖)^m) := by
        have hei := he i
        have hdi := hd i
        gcongr
        all_goals first | exact hFi t | exact hGi t | exact hf t | exact hg t
      _ = _ := by rw [pow_add]; ring

/-- Finite sums preserve polynomially weighted convergence. -/
theorem sum {κ : Type*} (s : Finset κ) {A : κ → ι → ℝ → ℂ} {a : κ → ℝ → ℂ}
    (h : ∀ j ∈ s, PolynomiallyWeightedLimit l (A j) (a j)) :
    PolynomiallyWeightedLimit l (fun i t => ∑ j ∈ s, A j i t) (fun t => ∑ j ∈ s, a j t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (const (l := l) 0)
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (Finset.mem_insert_self j s)).add
        (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

end PolynomiallyWeightedLimit

/-- All derivative orders of an ODE solution inherit the coefficient's weighted limit. -/
theorem polynomiallyWeightedLimit_iteratedDeriv_of_ode
    {ι : Type*} {l : Filter ι} {F A : ι → ℝ → ℂ} {f a : ℝ → ℂ}
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hA : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (A i)) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hodeF : ∀ i t, deriv (F i) t = A i t*F i t)
    (hodef : ∀ t, deriv f t = a t*f t)
    (hzero : PolynomiallyWeightedLimit l F f)
    (hcoeff : ∀ n, PolynomiallyWeightedLimit l
      (fun i => iteratedDeriv n (A i)) (iteratedDeriv n a)) :
    ∀ n, PolynomiallyWeightedLimit l
      (fun i => iteratedDeriv n (F i)) (iteratedDeriv n f) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hzero
    | succ n =>
      have hFi (i : ι) : iteratedDeriv (n+1) (F i) = fun t =>
          ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ)*iteratedDeriv j (A i) t*
            iteratedDeriv (n-j) (F i) t := by
        rw [iteratedDeriv_succ', show deriv (F i) = (fun t => A i t*F i t) from funext (hodeF i)]
        funext t
        exact iteratedDeriv_fun_mul ((hA i).contDiffAt.of_le (by exact_mod_cast le_top))
          ((hF i).contDiffAt.of_le (by exact_mod_cast le_top))
      have hfi : iteratedDeriv (n+1) f = fun t =>
          ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ)*iteratedDeriv j a t*
            iteratedDeriv (n-j) f t := by
        rw [iteratedDeriv_succ', show deriv f = (fun t => a t*f t) from funext hodef]
        funext t
        exact iteratedDeriv_fun_mul (ha.contDiffAt.of_le (by exact_mod_cast le_top))
          (hf.contDiffAt.of_le (by exact_mod_cast le_top))
      simp_rw [hFi, hfi]
      exact PolynomiallyWeightedLimit.sum (Finset.range (n+1)) (fun j _ =>
        ((PolynomiallyWeightedLimit.const (n.choose j : ℂ)).mul (hcoeff j)).mul
          (ih (n-j) (by omega)))

/-- Polynomially weighted convergence of every multiplier jet gives convergence on each fixed
Schwartz test in the full Schwartz topology. -/
theorem tendsto_schwartz_of_polynomiallyWeightedLimit
    {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hjet : ∀ n, PolynomiallyWeightedLimit l
      (fun i => iteratedDeriv n (F i)) (iteratedDeriv n f))
    (test : 𝓢(ℝ, ℂ)) (G : ι → 𝓢(ℝ, ℂ)) (g : 𝓢(ℝ, ℂ))
    (hG : ∀ i t, G i t=F i t*test t) (hg : ∀ t, g t=f t*test t) :
    Tendsto G l (𝓝 g) := by
  classical
  have hz : Tendsto (fun i => G i-g) l (𝓝 0) := by
    apply SchwartzMap.tendsto_zero_of_tendsto_seminorm
    intro a n
    choose k C e hC he ht hbound herr using hjet
    have hdecay (j : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ t,
        (1+‖t‖)^(a+k j)*‖iteratedDeriv (n-j) test t‖ ≤ D := by
      let D := 2^(a+k j)*(Finset.Iic (a+k j,n-j)).sup
        (fun m => SchwartzMap.seminorm ℂ m.1 m.2) test
      refine ⟨max 0 D, le_max_left _ _, fun t => ?_⟩
      have hb := SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℂ) (m := (a+k j,n-j)) le_rfl le_rfl test t
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hb
      exact hb.trans (le_max_right _ _)
    choose D hD hdecay using hdecay
    let E : ι → ℝ := fun i => ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*e j i*D j
    have hE0 (i : ι) : 0 ≤ E i := by
      exact Finset.sum_nonneg fun j _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (he j i)) (hD j)
    have hEt : Tendsto E l (𝓝 0) := by
      have h := tendsto_finsetSum (Finset.range (n+1)) (fun j _ =>
        ((ht j).const_mul (n.choose j : ℝ)).mul_const (D j))
      simpa only [mul_zero, zero_mul, Finset.sum_const_zero] using h
    apply squeeze_zero' (Eventually.of_forall fun i => apply_nonneg _ _) ?_ hEt
    have hall : ∀ᶠ i in l, ∀ j ∈ Finset.range (n+1),
        ∀ t, ‖iteratedDeriv j (F i) t-iteratedDeriv j f t‖ ≤ e j i*(1+‖t‖)^(k j) :=
      (Finset.eventually_all _).mpr (fun j _ => herr j)
    filter_upwards [hall] with i hi
    apply SchwartzMap.seminorm_le_bound' (𝕜 := ℂ) a n (G i-g) (hE0 i)
    intro t
    have hfun : (⇑(G i-g)) = fun x => (F i x-f x)*test x := by
      funext x
      change G i x-g x=(F i x-f x)*test x
      rw [hG, hg]
      ring
    have hsub (j : ℕ) : iteratedDeriv j (fun x => F i x-f x) t =
        iteratedDeriv j (F i) t-iteratedDeriv j f t :=
      iteratedDeriv_fun_sub ((hF i).contDiffAt.of_le (by exact_mod_cast le_top))
        (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [hfun, iteratedDeriv_fun_mul
      (((hF i).sub hf).contDiffAt.of_le (by exact_mod_cast le_top))
      (test.smooth n).contDiffAt]
    simp_rw [hsub]
    change ‖t‖^a*‖∑ j ∈ Finset.range (n+1),
      (n.choose j : ℂ)*(iteratedDeriv j (F i) t-iteratedDeriv j f t)*
        iteratedDeriv (n-j) test t‖ ≤ E i
    calc
      _ ≤ ‖t‖^a*∑ j ∈ Finset.range (n+1),
          ‖(n.choose j : ℂ)*(iteratedDeriv j (F i) t-iteratedDeriv j f t)*
            iteratedDeriv (n-j) test t‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (norm_nonneg _) _)
      _ = ∑ j ∈ Finset.range (n+1), ‖t‖^a*
          ‖(n.choose j : ℂ)*(iteratedDeriv j (F i) t-iteratedDeriv j f t)*
            iteratedDeriv (n-j) test t‖ := Finset.mul_sum _ _ _
      _ ≤ E i := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        calc
          _ ≤ (1+‖t‖)^a*((n.choose j : ℝ)*(e j i*(1+‖t‖)^(k j))*
              ‖iteratedDeriv (n-j) test t‖) := by
            apply mul_le_mul
              (pow_le_pow_left₀ (norm_nonneg t) (show ‖t‖ ≤ 1+‖t‖ by linarith) a)
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hi j hj t) (Nat.cast_nonneg _)) (norm_nonneg _))
              (by positivity) (by positivity)
          _ = (n.choose j : ℝ)*e j i*((1+‖t‖)^(a+k j)*
              ‖iteratedDeriv (n-j) test t‖) := by rw [pow_add]; ring
          _ ≤ (n.choose j : ℝ)*e j i*D j :=
            mul_le_mul_of_nonneg_left (hdecay j t) (mul_nonneg (Nat.cast_nonneg _) (he j i))
  simpa only [zero_add, sub_add_cancel] using hz.add_const g

end RHTower
