import GaloisForLFunctions.RHTower.ChronologicalTailKernelAnalytic
import GaloisForLFunctions.RHTower.ChronologicalHeatMellin
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Taylor coefficients of the Bose defect and jets of the heat residual

The analytic Bose defect `E(z) = 1/z - 1/(e^z - 1)` (with its removable value `E(0) = 1/2`) has

  `E^{(k)}(0) = -B_{k+1}/(k+1)`,  i.e. `E(z) = 1/2 - Σ_{j ≥ 1} B_{2j} z^{2j-1}/(2j)!`.

Proof: `F(z) = z E(z)` satisfies `F(z)(e^z - 1) = e^z - 1 - z` on the strip `|Im z| < 2π`.  Leibniz'
rule at `0` gives `Σ_{i<n} C(n,i) F^{(i)}(0) = [n ≥ 2]` for `n ≥ 1`, the recursion also satisfied
by `[i = 0] - B_i`; since the top coefficient `C(n, n-1) = n` is nonzero it determines
`F^{(i)}(0) = [i = 0] - B_i`, and `F^{(k+1)}(0) = (k+1) E^{(k)}(0)`.

Consequently the analytic extension `ρ_N(z) = e^{-z} + Σ_{k ≤ N} a_k E(kz)` of the heat residual has

  `ρ_N^{(n)}(0) = (-1)^n - B_{n+1}/(n+1) · Σ_{k ≤ N} a_k k^n`:

its value at `0` is `1 + ½ Σ a_k`, every even derivative of positive order is `1`, and the
derivative of order `2j - 1` is `-1 - B_{2j}/(2j) · Σ a_k k^{2j-1}`.
-/

open Complex Set Filter
open scoped Topology Nat
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section

namespace RHTower

/-! ### Iterated derivatives of dilations -/

/-- `(d/dw)^n f(cw) = c^n f^{(n)}(cw)` for every `f : ℂ → ℂ`. -/
theorem iteratedDeriv_comp_const_mul_complex (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w => f (c * w)) = fun w => c ^ n * iteratedDeriv n f (c * w) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field']
    beta_reduce
    rw [deriv_comp_mul_left (f := iteratedDeriv n f), iteratedDeriv_succ, smul_eq_mul, pow_succ]
    ring

/-! ### The Bernoulli coefficients -/

theorem zero_mem_boseStrip : (0 : ℂ) ∈ boseStrip := by
  rw [mem_boseStrip, Complex.zero_im, abs_zero]; positivity

theorem contDiffAt_boseKernelE {z : ℂ} (hz : z ∈ boseStrip) (n : ℕ) :
    ContDiffAt ℂ n boseKernelE z :=
  (boseKernelE_analyticOnNhd z hz).contDiffAt

/-- `z E(z) (e^z - 1) = e^z - 1 - z` on the strip. -/
theorem mul_boseKernelE_mul_exp_sub_one {z : ℂ} (hz : z ∈ boseStrip) :
    z * boseKernelE z * (Complex.exp z - 1) = Complex.exp z - 1 - z := by
  by_cases h0 : z = 0
  · subst h0; simp
  · rw [boseKernelE_of_ne h0, boseKernelC]
    have hden := exp_sub_one_ne_zero_of_mem_boseStrip hz h0
    field_simp

theorem iteratedDeriv_cexp (n : ℕ) : iteratedDeriv n Complex.exp = Complex.exp := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, Complex.deriv_exp]

/-- The Bernoulli recursion satisfied by the Taylor coefficients of `F(z) = z E(z)`. -/
theorem sum_choose_iteratedDeriv_mul_boseKernelE {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, (n.choose i : ℂ) *
        iteratedDeriv i (fun z => z * boseKernelE z) 0 = if n = 1 then 0 else 1 := by
  have hF : ∀ m : ℕ, ContDiffAt ℂ m (fun z => z * boseKernelE z) 0 := fun m =>
    contDiffAt_id.mul (contDiffAt_boseKernelE zero_mem_boseStrip m)
  have hG : ∀ m : ℕ, ContDiffAt ℂ m (fun z => Complex.exp z - 1) 0 := fun m =>
    (Complex.contDiff_exp.sub contDiff_const).contDiffAt
  have hGder : ∀ j : ℕ, iteratedDeriv j (fun z => Complex.exp z - 1) 0 = if j = 0 then 0 else 1 := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [iteratedDeriv_fun_sub Complex.contDiff_exp.contDiffAt contDiffAt_const, iteratedDeriv_cexp,
        iteratedDeriv_const, if_neg hj.ne', if_neg hj.ne']
      simp
  have hev : (fun z => (z * boseKernelE z) * (Complex.exp z - 1)) =ᶠ[𝓝 (0 : ℂ)]
      fun z => Complex.exp z - 1 - z :=
    Filter.eventuallyEq_of_mem (isOpen_boseStrip.mem_nhds zero_mem_boseStrip)
      fun z hz => mul_boseKernelE_mul_exp_sub_one hz
  have hlhs := iteratedDeriv_fun_mul (hF n) (hG n) (x := (0 : ℂ))
  rw [hev.iteratedDeriv_eq] at hlhs
  have hrhs : iteratedDeriv n (fun z => Complex.exp z - 1 - z) 0 = if n = 1 then 0 else 1 := by
    rw [iteratedDeriv_fun_sub (f := fun z => Complex.exp z - 1) (g := fun z : ℂ => z)
        ((Complex.contDiff_exp.sub contDiff_const).contDiffAt) contDiffAt_id,
      iteratedDeriv_fun_sub (f := Complex.exp) (g := fun _ : ℂ => (1 : ℂ))
        Complex.contDiff_exp.contDiffAt contDiffAt_const, iteratedDeriv_cexp,
      iteratedDeriv_const, iteratedDeriv_fun_id]
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, if_false, Complex.exp_zero, sub_zero]
    split_ifs <;> simp
  rw [hrhs, Finset.sum_range_succ, hGder, Nat.sub_self, if_pos rfl, mul_zero, add_zero] at hlhs
  rw [hlhs]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : n - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
  rw [hGder, if_neg hi', mul_one]

/-- `F^{(i)}(0) = [i = 0] - B_i` for `F(z) = z E(z)`. -/
theorem iteratedDeriv_mul_boseKernelE_zero (i : ℕ) :
    iteratedDeriv i (fun z => z * boseKernelE z) 0 = (if i = 0 then 1 else 0) - bernoulli i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hrec := sum_choose_iteratedDeriv_mul_boseKernelE (n := i + 1) (by omega)
    have hbernC : ∑ k ∈ Finset.range (i + 1), ((i + 1).choose k : ℂ) * (bernoulli k : ℂ) =
        if i = 0 then 1 else 0 := by
      have := congrArg (fun q : ℚ => (q : ℂ)) (sum_bernoulli (i + 1))
      simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast] at this
      rw [this]
      by_cases hi : i = 0 <;> simp [hi]
    have hind : ∑ k ∈ Finset.range (i + 1), ((i + 1).choose k : ℂ) * (if k = 0 then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos i)) h
    have hrec' : ∑ k ∈ Finset.range (i + 1), ((i + 1).choose k : ℂ) *
        iteratedDeriv k (fun z => z * boseKernelE z) 0 = if i = 0 then 0 else 1 := by
      rw [hrec]; by_cases hi : i = 0 <;> simp [hi]
    rw [Finset.sum_range_succ] at hrec' hbernC hind
    have hlow : ∑ k ∈ Finset.range i, ((i + 1).choose k : ℂ) *
        iteratedDeriv k (fun z => z * boseKernelE z) 0 =
        ∑ k ∈ Finset.range i, ((i + 1).choose k : ℂ) * (if k = 0 then 1 else 0) -
          ∑ k ∈ Finset.range i, ((i + 1).choose k : ℂ) * (bernoulli k : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_range.mp hk)]; ring
    rw [hlow] at hrec'
    have hchoose : ((i + 1).choose i : ℂ) = i + 1 := by
      rw [Nat.choose_succ_self_right]; push_cast; ring
    rw [hchoose] at hrec' hbernC hind
    have hne : (i + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    apply mul_left_cancel₀ hne
    have key : (i + 1 : ℂ) * iteratedDeriv i (fun z => z * boseKernelE z) 0 =
        (i + 1 : ℂ) * (if i = 0 then 1 else 0) - (i + 1 : ℂ) * (bernoulli i : ℂ) := by
      by_cases hi : i = 0
      · simp only [hi, if_true] at hrec' hbernC hind ⊢
        linear_combination hrec' - hind + hbernC
      · simp only [hi, if_false] at hrec' hbernC hind ⊢
        linear_combination hrec' - hind + hbernC
    rw [key]; ring

/-- **Taylor coefficients of the Bose defect.** `E^{(k)}(0) = -B_{k+1}/(k+1)`. -/
theorem iteratedDeriv_boseKernelE_zero (k : ℕ) :
    iteratedDeriv k boseKernelE 0 = -(bernoulli (k + 1) : ℂ) / (k + 1) := by
  have hF := iteratedDeriv_mul_boseKernelE_zero (k + 1)
  have hid : ContDiffAt ℂ (k + 1 : ℕ) (fun z : ℂ => z) 0 := contDiffAt_id
  rw [iteratedDeriv_fun_mul hid (contDiffAt_boseKernelE zero_mem_boseStrip (k + 1)),
    Finset.sum_eq_single 1] at hF
  · rw [iteratedDeriv_fun_id_zero, if_pos rfl, Nat.choose_one_right, Nat.add_sub_cancel,
      if_neg (Nat.succ_ne_zero k)] at hF
    have hne : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [eq_div_iff hne]
    push_cast at hF
    linear_combination hF
  · intro i _ hi
    rw [iteratedDeriv_fun_id_zero, if_neg hi]; simp
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem boseKernelE_zero : boseKernelE 0 = 1 / 2 := by
  have := iteratedDeriv_boseKernelE_zero 0
  rw [iteratedDeriv_zero] at this
  rw [this, zero_add, bernoulli_one]; push_cast; ring

/-- `B_{2j} ≠ 0` for `j ≥ 1` (Euler's formula for `ζ(2j)`). -/
theorem bernoulli_two_mul_ne_zero {j : ℕ} (hj : j ≠ 0) : bernoulli (2 * j) ≠ 0 := by
  intro h0
  have hz := riemannZeta_two_mul_nat hj
  rw [h0, Rat.cast_zero, mul_zero, zero_div] at hz
  exact riemannZeta_ne_zero_of_one_lt_re (by
    rw [show ((2 : ℂ) * (j : ℂ)) = ((2 * j : ℕ) : ℂ) by push_cast; ring, Complex.natCast_re]
    exact_mod_cast (by omega : 1 < 2 * j)) hz

/-! ### Jets of the analytic heat residual -/

/-- The analytic extension `ρ_N(z) = e^{-z} + Σ_{k ≤ N} a_k E(kz)` of the heat residual. -/
def heatErrorExt (a : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-z) + ∑ k ∈ Finset.Ioc 0 N, (a k : ℂ) * boseKernelE (k * z)

theorem heatErrorExt_ofReal (a : ℕ → ℝ) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    heatErrorExt a N t = (chronologicalHeatError a N t : ℂ) := by
  rw [heatErrorExt, chronologicalHeatError]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
  rw [show ((k : ℂ) * (t : ℂ)) = ((k * t : ℝ) : ℂ) by push_cast; ring,
    boseKernelE_ofReal (mul_pos hk0 ht)]

theorem mul_mem_boseStrip_nhds (k : ℕ) : ∀ᶠ z : ℂ in 𝓝 0, (k : ℂ) * z ∈ boseStrip :=
  (isOpen_boseStrip.preimage (continuous_const.mul continuous_id)).mem_nhds
    (by simpa using zero_mem_boseStrip)

/-- **Jets of the analytic residual.** `ρ_N^{(n)}(0) = (-1)^n - B_{n+1}/(n+1) · Σ a_k k^n`. -/
theorem iteratedDeriv_heatErrorExt_zero (a : ℕ → ℝ) (N n : ℕ) :
    iteratedDeriv n (heatErrorExt a N) 0 =
      (-1) ^ n - (bernoulli (n + 1) : ℂ) / (n + 1) *
        ∑ k ∈ Finset.Ioc 0 N, (a k : ℂ) * (k : ℂ) ^ n := by
  have hterm : ∀ k : ℕ, ContDiffAt ℂ n (fun z => (a k : ℂ) * boseKernelE (k * z)) 0 := by
    intro k
    refine contDiffAt_const.mul ?_
    have h0 : (k : ℂ) * 0 ∈ boseStrip := by simpa using zero_mem_boseStrip
    exact (contDiffAt_boseKernelE h0 n).comp 0 (contDiffAt_const.mul contDiffAt_id)
  have hexp : ContDiffAt ℂ n (fun z => Complex.exp (-z)) 0 :=
    (Complex.contDiff_exp.comp contDiff_neg).contDiffAt
  have hsum : ContDiffAt ℂ n (fun z => ∑ k ∈ Finset.Ioc 0 N, (a k : ℂ) * boseKernelE (k * z)) 0 :=
    ContDiffAt.sum fun k _ => hterm k
  rw [show heatErrorExt a N = fun z => Complex.exp (-z) +
      ∑ k ∈ Finset.Ioc 0 N, (a k : ℂ) * boseKernelE (k * z) from rfl,
    iteratedDeriv_fun_add (f := fun z => Complex.exp (-z))
      (g := fun z => ∑ k ∈ Finset.Ioc 0 N, (a k : ℂ) * boseKernelE (k * z)) hexp hsum,
    iteratedDeriv_fun_sum fun k _ => hterm k]
  have hexpder : iteratedDeriv n (fun z => Complex.exp (-z)) 0 = (-1) ^ n := by
    have := iteratedDeriv_cexp_const_mul n (-1)
    simp only [neg_one_mul] at this
    rw [this]; simp
  have hkder : ∀ k : ℕ, iteratedDeriv n (fun z => (a k : ℂ) * boseKernelE (k * z)) 0 =
      (a k : ℂ) * (k : ℂ) ^ n * (-(bernoulli (n + 1) : ℂ) / (n + 1)) := by
    intro k
    have h1 := iteratedDeriv_const_mul_field (n := n) (x := (0 : ℂ)) (a k : ℂ)
      (fun z => boseKernelE (k * z))
    have h2 := congrFun (iteratedDeriv_comp_const_mul_complex boseKernelE (k : ℂ) n) 0
    beta_reduce at h2
    rw [h1, h2, mul_zero, iteratedDeriv_boseKernelE_zero]
    ring
  rw [hexpder, Finset.sum_congr rfl fun k _ => hkder k, Finset.mul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_ofReal_mul_pow (a : ℕ → ℝ) (N n : ℕ) :
    ∑ k ∈ Finset.Ioc 0 N, (a k : ℂ) * (k : ℂ) ^ n =
      ((∑ k ∈ Finset.Ioc 0 N, a k * (k : ℝ) ^ n : ℝ) : ℂ) := by
  push_cast; rfl

/-- **The jets of a moment-matched row.**  If `Σ a_k = -2` and `Σ a_k k^{2j-1} = -2j/B_{2j}` for
`1 ≤ j ≤ m`, the analytic residual vanishes at `0` together with its odd derivatives of orders
`1, 3, …, 2m - 1`, while every even derivative of positive order equals `1`. -/
theorem heatErrorExt_jets {a : ℕ → ℝ} {N m : ℕ}
    (hsum : ∑ k ∈ Finset.Ioc 0 N, a k = -2)
    (hodd : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      ∑ k ∈ Finset.Ioc 0 N, a k * (k : ℝ) ^ (2 * j - 1) = -(2 * j) / (bernoulli (2 * j) : ℝ)) :
    heatErrorExt a N 0 = 0 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ m → iteratedDeriv (2 * j - 1) (heatErrorExt a N) 0 = 0) ∧
      (∀ j : ℕ, 1 ≤ j → iteratedDeriv (2 * j) (heatErrorExt a N) 0 = 1) := by
  refine ⟨?_, fun j hj hjm => ?_, fun j hj => ?_⟩
  · have h := iteratedDeriv_heatErrorExt_zero a N 0
    rw [iteratedDeriv_zero] at h
    rw [h, sum_ofReal_mul_pow]
    simp only [pow_zero, mul_one, hsum, zero_add, bernoulli_one]
    push_cast; ring
  · rw [iteratedDeriv_heatErrorExt_zero, sum_ofReal_mul_pow, hodd j hj hjm]
    have hB : (bernoulli (2 * j) : ℂ) ≠ 0 := by
      exact_mod_cast bernoulli_two_mul_ne_zero (by omega)
    have hodd' : Odd (2 * j - 1) := ⟨j - 1, by omega⟩
    rw [show 2 * j - 1 + 1 = 2 * j by omega, hodd'.neg_one_pow]
    push_cast
    have hn : ((2 * j - 1 : ℕ) : ℂ) + 1 = 2 * j := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hn]
    have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    field_simp
    ring
  · rw [iteratedDeriv_heatErrorExt_zero, bernoulli_eq_zero_of_odd ⟨j, rfl⟩ (by omega)]
    simp [(even_two_mul j).neg_one_pow]

end RHTower
