import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMellinTransformOfAStencil
import GaloisForLFunctions.RigidArithmeticOfCuts.TheFakePrimeMeasureIsUnique
import Mathlib.FieldTheory.Fixed

/-!
# Zeros are the kernel of the cut system

Read the cut system at the power measure `U_s(r) = r^{-s} − (r + 1)^{-s}`:

`Σ_r U_s(r) (r mod k) = (1 − k^{1-s}) ζ(s)`,  `Re s > 0`, `s ≠ 1`.

So `U_s` solves the homogeneous system at every `k` exactly when `ζ(s) = 0`. The zero modes are the
power-law solutions, and every finite combination of power measures in the kernel is a combination of
zero modes, by independence of the characters `k ↦ k^w`. This is why no stencil identity excludes a
zero: the cut system has them as solutions.

**Positivity reaches exactly the edge.** A solution of the homogeneous system bounded below by
`−1/(r (r + 1))` is zero, by the uniqueness of the fake. On `Re s ≥ 1` the mode `U_s` is dominated by
the pronic measure, so `ζ(s) ≠ 0` there. On `Re s < 1` it dominates the pronic measure at large `r`,
and positivity says nothing. Real zeros are excluded for the same reason: a real mode has one sign.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-! ### The cut moment of a power measure -/

/-- The sawtooth stencil `δ₁ − k δ_k`, whose multiplicity is `r mod k`. -/
def sawStencil (k : ℕ) : ℕ →₀ ℤ := Finsupp.single 1 1 - Finsupp.single k (k : ℤ)

private lemma stepWeight_eq_sum' (c : ℕ →₀ ℤ) (m : ℕ) :
    stepWeight c m = c.sum fun k a => a * ((m / k : ℕ) : ℤ) := rfl

private lemma balance_eq_sum' (c : ℕ →₀ ℤ) :
    ∑ k ∈ c.support, (c k : ℝ) / k = c.sum fun k a => (a : ℝ) / k := rfl

private lemma dirichletPoly_eq_sum (c : ℕ →₀ ℤ) (s : ℂ) :
    dirichletPoly c s = c.sum fun k a => (a : ℂ) * ((k : ℝ) : ℂ) ^ (-s) := rfl

theorem sawStencil_zero {k : ℕ} (hk : 2 ≤ k) : sawStencil k 0 = 0 := by
  simp only [sawStencil, Finsupp.coe_sub, Pi.sub_apply]
  rw [Finsupp.single_eq_of_ne (by omega), Finsupp.single_eq_of_ne (by omega)]
  rfl

theorem isBalanced_sawStencil {k : ℕ} (hk : 2 ≤ k) : IsBalanced (sawStencil k) := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [IsBalanced, balance_eq_sum', sawStencil, Finsupp.sum_sub_index (by intro _ a b; push_cast; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  push_cast
  field_simp
  ring

/-- The multiplicity of the sawtooth stencil is the sawtooth. -/
theorem stepWeight_sawStencil {k : ℕ} (_hk : 2 ≤ k) (r : ℕ) :
    stepWeight (sawStencil k) r = ((r % k : ℕ) : ℤ) := by
  rw [stepWeight_eq_sum', sawStencil, Finsupp.sum_sub_index (by intro _ a b; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  have h := Nat.div_add_mod r k
  have h' : (k : ℤ) * ((r / k : ℕ) : ℤ) + ((r % k : ℕ) : ℤ) = r := by exact_mod_cast h
  simp only [Nat.div_one, one_mul]
  linarith

/-- The Dirichlet polynomial of the sawtooth stencil. -/
theorem dirichletPoly_sawStencil {k : ℕ} (hk : 2 ≤ k) (s : ℂ) :
    dirichletPoly (sawStencil k) s = 1 - ((k : ℝ) : ℂ) ^ (1 - s) := by
  have hkC : ((k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : k ≠ 0)
  rw [dirichletPoly_eq_sum, sawStencil, Finsupp.sum_sub_index (by intro _ a b; push_cast; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  have hpow : ((k : ℝ) : ℂ) ^ (1 - s) = ((k : ℝ) : ℂ) * ((k : ℝ) : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hkC, Complex.cpow_one]
  rw [hpow]
  simp

/-- **The cut moment of a power measure.** -/
theorem hasSum_abelStep_mod {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    HasSum (fun j : ℕ => abelStep s j * (((j + 1) % k : ℕ) : ℂ))
      ((1 - ((k : ℝ) : ℂ) ^ (1 - s)) * riemannZeta s) := by
  have h := hasSum_mellin (sawStencil_zero hk) (isBalanced_sawStencil hk) hσ hs1
  rw [dirichletPoly_sawStencil hk] at h
  have hfun : (fun j : ℕ => (stepWeight (sawStencil k) (j + 1) : ℂ) * abelStep s j) =
      fun j : ℕ => abelStep s j * (((j + 1) % k : ℕ) : ℂ) := by
    funext j
    rw [stepWeight_sawStencil hk, mul_comm]
    push_cast
    rfl
  rwa [hfun] at h

/-! ### The power-law kernel -/

/-- A power with every `k ≥ 2` giving `1` has exponent zero. -/
theorem eq_zero_of_forall_cpow_eq_one {w : ℂ} (h : ∀ k : ℕ, 2 ≤ k → ((k : ℝ) : ℂ) ^ w = 1) :
    w = 0 := by
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, 2 ≤ k ∧ ‖w‖ < k := by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖w‖
    exact ⟨max 2 n, le_max_left _ _, hn.trans_le (by exact_mod_cast le_max_right _ _)⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk0' : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hne : ∀ n : ℕ, 2 ≤ n → ((n : ℝ) : ℂ) ≠ 0 := fun n hn => by exact_mod_cast (by omega : n ≠ 0)
  have h1 := h k hk1
  have h2 := h (k + 1) (by omega)
  rw [Complex.cpow_def_of_ne_zero (hne k hk1), ← Complex.ofReal_log hk0.le] at h1
  rw [Complex.cpow_def_of_ne_zero (hne (k + 1) (by omega)), ← Complex.ofReal_log hk0'.le] at h2
  set L : ℝ := Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) with hL
  have hLpos : 0 < L := by
    rw [hL, sub_pos]
    exact Real.log_lt_log hk0 (by push_cast; linarith)
  have hLle : L ≤ 1 / (k : ℝ) := by
    rw [hL, ← Real.log_div hk0'.ne' hk0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hk0' hk0)
    refine this.trans (le_of_eq ?_)
    push_cast
    field_simp
    ring
  have hexp : Complex.exp ((L : ℂ) * w) = 1 := by
    have : (L : ℂ) * w = ((Real.log ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) * w - ((Real.log (k : ℝ) : ℝ) : ℂ) * w := by
      rw [hL]
      push_cast
      ring
    rw [this, Complex.exp_sub, h1, h2, div_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hnorm : L * ‖w‖ = |(n : ℝ)| * (2 * Real.pi) := by
    have := congrArg norm hn
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos, Complex.norm_intCast,
      Complex.norm_I, mul_one, abs_of_pos Real.pi_pos] at this
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2] at this
    exact this
  have hsmall : L * ‖w‖ < 1 := by
    calc L * ‖w‖ ≤ 1 / (k : ℝ) * ‖w‖ := mul_le_mul_of_nonneg_right hLle (norm_nonneg w)
      _ < 1 / (k : ℝ) * (k : ℝ) := mul_lt_mul_of_pos_left hk2 (by positivity)
      _ = 1 := by field_simp
  have hn0 : n = 0 := by
    by_contra hne0
    have h3 : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hne0
    have h4 := Real.pi_gt_three
    nlinarith
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul] at hn
  exact (mul_eq_zero.mp hn).resolve_left (by exact_mod_cast hLpos.ne')

/-- **Zeros are the power-law kernel.** `U_s` solves the homogeneous cut system iff `ζ(s) = 0`. -/
theorem forall_hasSum_abelStep_mod_zero_iff {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    (∀ k : ℕ, 2 ≤ k → HasSum (fun j : ℕ => abelStep s j * (((j + 1) % k : ℕ) : ℂ)) 0) ↔
      riemannZeta s = 0 := by
  constructor
  · intro h
    by_contra hζ
    have hone : ∀ k : ℕ, 2 ≤ k → ((k : ℝ) : ℂ) ^ (1 - s) = 1 := by
      intro k hk
      have := (hasSum_abelStep_mod hk hσ hs1).unique (h k hk)
      have h1 := (mul_eq_zero.mp this).resolve_right hζ
      linear_combination -h1
    have h0 := eq_zero_of_forall_cpow_eq_one hone
    exact hs1 (by linear_combination -h0)
  · intro hζ k hk
    have h := hasSum_abelStep_mod hk hσ hs1
    rwa [hζ, mul_zero] at h

/-! ### Finite combinations of modes -/

/-- The character `k ↦ k^w` of the multiplicative monoid of positive integers. -/
def powerChar (w : ℂ) : ℕ+ →* ℂ where
  toFun k := (((k : ℕ) : ℝ) : ℂ) ^ w
  map_one' := by simp
  map_mul' a b := by
    have h := Complex.natCast_mul_natCast_cpow (a : ℕ) (b : ℕ) w
    simpa using h

theorem powerChar_injective : Function.Injective powerChar := by
  intro v w h
  have hone : ∀ k : ℕ, 2 ≤ k → ((k : ℝ) : ℂ) ^ (v - w) = 1 := by
    intro k hk
    have hk' : 0 < k := by omega
    have hne : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk'.ne'
    have h1 : powerChar v ⟨k, hk'⟩ = powerChar w ⟨k, hk'⟩ := by rw [h]
    change ((k : ℝ) : ℂ) ^ v = ((k : ℝ) : ℂ) ^ w at h1
    rw [Complex.cpow_sub _ _ hne, h1, div_self (Complex.cpow_ne_zero_iff.mpr (Or.inl hne))]
  exact sub_eq_zero.mp (eq_zero_of_forall_cpow_eq_one hone)

/-- Independence of the power characters, with the constant character removed. -/
theorem eq_zero_of_sum_mul_one_sub_cpow {W : Finset ℂ} (h0 : (0 : ℂ) ∉ W) {A : ℂ → ℂ}
    (h : ∀ k : ℕ+, ∑ w ∈ W, A w * (1 - (((k : ℕ) : ℝ) : ℂ) ^ w) = 0) {w : ℂ} (hw : w ∈ W) :
    A w = 0 := by
  classical
  have hli : LinearIndependent ℂ (fun v : ℂ => (powerChar v : ℕ+ → ℂ)) :=
    (linearIndependent_monoidHom ℕ+ ℂ).comp powerChar powerChar_injective
  set g : ℂ → ℂ := fun v => if v = 0 then ∑ w ∈ W, A w else -A v with hg
  have hsum : ∑ v ∈ insert (0 : ℂ) W, g v • (powerChar v : ℕ+ → ℂ) = 0 := by
    funext k
    have hne : ∀ v ∈ W, g v = -A v := fun v hv => by
      have : v ≠ 0 := fun he => h0 (he ▸ hv)
      simp [hg, this]
    rw [sum_insert h0, Pi.add_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hc : (powerChar 0 : ℕ+ → ℂ) k = 1 := by
      change (((k : ℕ) : ℝ) : ℂ) ^ (0 : ℂ) = 1
      simp
    rw [hc, mul_one, Finset.sum_congr rfl fun v hv => by rw [hne v hv]]
    have h1 := h k
    simp only [mul_sub, mul_one, sum_sub_distrib] at h1
    have h2 : ∑ v ∈ W, -A v * (powerChar v : ℕ+ → ℂ) k =
        -∑ v ∈ W, A v * (((k : ℕ) : ℝ) : ℂ) ^ v := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun v _ => by
        change -A v * (((k : ℕ) : ℝ) : ℂ) ^ v = _
        ring
    rw [h2]
    simp only [hg, if_true]
    linear_combination h1
  have hgw := linearIndependent_iff'.mp hli (insert (0 : ℂ) W) g hsum w (mem_insert_of_mem hw)
  have hne : w ≠ 0 := fun he => h0 (he ▸ hw)
  simpa [hg, hne] using hgw

/-- **The finite part of the kernel is spanned by zeros.** A finite combination of power measures with
distinct exponents solves the homogeneous cut system only if every mode with a nonzero coefficient is
a zero. -/
theorem riemannZeta_eq_zero_of_finite_kernel {S : Finset ℂ} (hσ : ∀ s ∈ S, 0 < s.re)
    (hs1 : ∀ s ∈ S, s ≠ 1) {c : ℂ → ℂ}
    (hker : ∀ k : ℕ, 2 ≤ k → HasSum (fun j : ℕ => ∑ s ∈ S, c s * (abelStep s j *
      (((j + 1) % k : ℕ) : ℂ))) 0) {s : ℂ} (hs : s ∈ S) (hc : c s ≠ 0) : riemannZeta s = 0 := by
  classical
  have hval : ∀ k : ℕ, 2 ≤ k →
      ∑ s ∈ S, c s * ((1 - ((k : ℝ) : ℂ) ^ (1 - s)) * riemannZeta s) = 0 := fun k hk =>
    (hasSum_sum fun s hs => (hasSum_abelStep_mod hk (hσ s hs) (hs1 s hs)).mul_left (c s)).unique
      (hker k hk)
  set W : Finset ℂ := S.image (fun s => 1 - s) with hW
  have hinj : Set.InjOn (fun s : ℂ => 1 - s) (S : Set ℂ) := fun a _ b _ hab => by
    simpa using hab
  have h0 : (0 : ℂ) ∉ W := by
    intro h
    obtain ⟨t, ht, hzero⟩ := mem_image.mp h
    exact hs1 t ht (by linear_combination -hzero)
  set A : ℂ → ℂ := fun w => c (1 - w) * riemannZeta (1 - w) with hA
  have hmem : 1 - s ∈ W := mem_image_of_mem _ hs
  have hsumW : ∀ k : ℕ+, ∑ w ∈ W, A w * (1 - (((k : ℕ) : ℝ) : ℂ) ^ w) = 0 := by
    intro k
    rw [hW, sum_image hinj]
    simp only [hA, sub_sub_cancel]
    rcases Nat.lt_or_ge (k : ℕ) 2 with hk | hk
    · have hk1 : (k : ℕ) = 1 := by have := k.pos; omega
      simp [hk1]
    · rw [← hval k hk]
      exact sum_congr rfl fun t _ => by ring
  have hAs := eq_zero_of_sum_mul_one_sub_cpow h0 hsumW hmem
  simp only [hA, sub_sub_cancel] at hAs
  exact (mul_eq_zero.mp hAs).resolve_left hc

/-! ### Positivity reaches exactly the edge -/

/-- **A homogeneous solution above the pronic floor is zero.** -/
theorem eq_zero_of_homogeneous_of_ge {v : ℕ → ℝ}
    (hlow : ∀ j : ℕ, -(1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) ≤ v j)
    (hmom : ∀ k : ℕ, 1 ≤ k → HasSum (fun j => v j * (((j + 1) % k : ℕ) : ℝ)) 0) (j : ℕ) :
    v j = 0 := by
  have hu : ∀ K, IsFakePrimeMeasure K fun j : ℕ => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) + v j := by
    intro K
    refine ⟨fun j => by linarith [hlow j], fun k hk => ?_⟩
    have h := ((isFakePrimeMeasure_pronic K).moment k hk).add (hmom k (mem_Icc.mp hk).1)
    rw [add_zero] at h
    have hfun : (fun j : ℕ => (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) + v j) * (((j + 1) % k : ℕ) : ℝ)) =
        fun j : ℕ => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * (((j + 1) % k : ℕ) : ℝ) +
          v j * (((j + 1) % k : ℕ) : ℝ) := by
      funext j
      ring
    rwa [hfun]
  have := eq_pronic_of_forall_isFakePrimeMeasure hu j
  linarith

/-- The moment at `k = 1` is trivial. -/
private lemma hasSum_mod_one (v : ℕ → ℝ) : HasSum (fun j => v j * (((j + 1) % 1 : ℕ) : ℝ)) 0 := by
  simp [Nat.mod_one, hasSum_zero]

/-- At a zero, the real and imaginary parts of the mode solve the homogeneous system. -/
private lemma hasSum_re_abelStep {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) (hζ : riemannZeta s = 0)
    {k : ℕ} (hk : 1 ≤ k) : HasSum (fun j => (abelStep s j).re * (((j + 1) % k : ℕ) : ℝ)) 0 := by
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · have : k = 1 := by omega
    subst this
    exact hasSum_mod_one _
  · have h := (forall_hasSum_abelStep_mod_zero_iff hσ hs1).mpr hζ k h2
    have hre := Complex.reCLM.hasSum h
    simpa [Complex.mul_re] using hre

private lemma hasSum_im_abelStep {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) (hζ : riemannZeta s = 0)
    {k : ℕ} (hk : 1 ≤ k) : HasSum (fun j => (abelStep s j).im * (((j + 1) % k : ℕ) : ℝ)) 0 := by
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · have : k = 1 := by omega
    subst this
    exact hasSum_mod_one _
  · have h := (forall_hasSum_abelStep_mod_zero_iff hσ hs1).mpr hζ k h2
    have him := Complex.imCLM.hasSum h
    simpa [Complex.mul_im] using him

/-- **The edge from the cut system.** On `Re s ≥ 1` the mode is dominated by the pronic measure, so
positivity excludes it. -/
theorem riemannZeta_ne_zero_of_one_le_re_of_cut {s : ℂ} (h1 : 1 ≤ s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hζ
  have hσ : 0 < s.re := by linarith
  have hs0 : 0 < ‖s‖ := norm_pos_iff.mpr fun he => by simp [he] at hσ
  set c : ℝ := 1 / (2 * ‖s‖) with hc
  have hc0 : 0 < c := by positivity
  have hbound : ∀ j : ℕ, c * ‖abelStep s j‖ ≤ 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    intro j
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have h2 := norm_abelStep_le_rpow hσ j
    have h3 : ((j : ℝ) + 1) ^ (-s.re - 1) ≤ ((j : ℝ) + 1) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hj (by linarith)
    have h4 : ((j : ℝ) + 1) ^ (-2 : ℝ) = 1 / ((j : ℝ) + 1) ^ 2 := by
      rw [Real.rpow_neg (by linarith), one_div]
      norm_num
    have h5 : c * ‖abelStep s j‖ ≤ 1 / 2 * (1 / ((j : ℝ) + 1) ^ 2) := by
      calc c * ‖abelStep s j‖ ≤ c * (‖s‖ * ((j : ℝ) + 1) ^ (-s.re - 1)) := by gcongr
        _ ≤ c * (‖s‖ * (1 / ((j : ℝ) + 1) ^ 2)) := by rw [← h4]; gcongr
        _ = _ := by rw [hc]; field_simp
    refine h5.trans ?_
    have hp : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    have hq : (0 : ℝ) < (j : ℝ) + 2 := by linarith
    have hrew : (1 : ℝ) / 2 * (1 / ((j : ℝ) + 1) ^ 2) = 1 / (2 * ((j : ℝ) + 1) ^ 2) := by
      field_simp
    rw [hrew]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hre : ∀ j, (abelStep s j).re = 0 := by
    intro j
    have h := eq_zero_of_homogeneous_of_ge (v := fun j => c * (abelStep s j).re) (fun j => ?_)
      (fun k hk => ?_) j
    · exact (mul_eq_zero.mp h).resolve_left hc0.ne'
    · have h2 := hbound j
      have h3 : |(abelStep s j).re| ≤ ‖abelStep s j‖ := Complex.abs_re_le_norm _
      have h4 := neg_abs_le (abelStep s j).re
      have h5 : c * -‖abelStep s j‖ ≤ c * (abelStep s j).re :=
        mul_le_mul_of_nonneg_left (by linarith) hc0.le
      linarith
    · have h := (hasSum_re_abelStep hσ hs1 hζ hk).mul_left c
      rw [mul_zero] at h
      simpa only [mul_assoc] using h
  have him : ∀ j, (abelStep s j).im = 0 := by
    intro j
    have h := eq_zero_of_homogeneous_of_ge (v := fun j => c * (abelStep s j).im) (fun j => ?_)
      (fun k hk => ?_) j
    · exact (mul_eq_zero.mp h).resolve_left hc0.ne'
    · have h2 := hbound j
      have h3 : |(abelStep s j).im| ≤ ‖abelStep s j‖ := Complex.abs_im_le_norm _
      have h4 := neg_abs_le (abelStep s j).im
      have h5 : c * -‖abelStep s j‖ ≤ c * (abelStep s j).im :=
        mul_le_mul_of_nonneg_left (by linarith) hc0.le
      linarith
    · have h := (hasSum_im_abelStep hσ hs1 hζ hk).mul_left c
      rw [mul_zero] at h
      simpa only [mul_assoc] using h
  have h0 : abelStep s 0 = 0 := Complex.ext (hre 0) (him 0)
  rw [abelStep] at h0
  have h2 : (((((0 : ℕ) : ℝ) + 2 : ℝ) : ℂ)) ^ (-s) = 1 := by
    have h3 := sub_eq_zero.mp h0
    rw [← h3]
    simp
  have hnorm := congrArg norm h2
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), norm_one] at hnorm
  simp only [Nat.cast_zero, zero_add, Complex.neg_re] at hnorm
  have hlt : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

/-- **The cut system excludes real zeros.** A real mode has one sign. -/
theorem riemannZeta_ne_zero_of_real {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro hζ
  have hσ : 0 < ((σ : ℝ) : ℂ).re := by simpa using h0
  have hs1 : ((σ : ℝ) : ℂ) ≠ 1 := by
    intro h
    have : σ = 1 := by exact_mod_cast h
    linarith
  have hval : ∀ j : ℕ, (abelStep (σ : ℂ) j).re = ((j : ℝ) + 1) ^ (-σ) - ((j : ℝ) + 2) ^ (-σ) := by
    intro j
    rw [abelStep, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (by positivity),
      ← Complex.ofReal_cpow (by positivity)]
    simp
  have hpos : ∀ j : ℕ, 0 < (abelStep (σ : ℂ) j).re := by
    intro j
    rw [hval, sub_pos]
    exact Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
  have h := eq_zero_of_homogeneous_of_ge (v := fun j => (abelStep (σ : ℂ) j).re)
    (fun j => (neg_nonpos.mpr (by positivity)).trans (hpos j).le)
    (fun k hk => hasSum_re_abelStep hσ hs1 hζ hk) 0
  exact (hpos 0).ne' h

/-! ### The Hecke action on the kernel -/

/-- **The kernel is Hecke invariant.** -/
theorem IsCutKernel.dilate {W : ℕ → ℝ} (hW : IsCutKernel W) {j : ℕ} (hj : 1 ≤ j) :
    IsCutKernel fun r => W (j * r) := by
  intro k hk
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hid : ∀ J, cutDefect (fun r => W (j * r)) k J =
      (cutDefect W (j * k) J - cutDefect W j (k * J)) / j := by
    intro J
    simp only [cutDefect]
    have hreindex : ∀ i, W (j * (k * i)) = W (j * k * i) := fun i => by rw [mul_assoc]
    simp only [hreindex]
    rw [show j * (k * J) = j * k * J by ring]
    push_cast
    field_simp
    ring
  have h1 := hW (j * k) (Nat.mul_pos hj hk)
  have hN : Tendsto (fun J : ℕ => k * J) atTop atTop := tendsto_id.const_mul_atTop' hk
  have h2 := (hW j hj).comp hN
  have h3 := (h1.sub h2).div_const (j : ℝ)
  simp only [sub_zero, zero_div] at h3
  exact h3.congr fun J => (hid J).symm

/-! ### Multiplicative kernel vectors -/

/-- The cut defect of a complex function. -/
def cutDefectC (T : ℕ → ℂ) (k J : ℕ) : ℂ :=
  ∑ r ∈ Icc 1 (k * J), T r - (k : ℂ) * ∑ j ∈ Icc 1 J, T (k * j)

/-- **The cut value of a completely multiplicative tail.** With convergent partial sums the cut value
is `(1 − k T(k)) L`. -/
theorem tendsto_cutDefectC_of_mul {T : ℕ → ℂ} (hT : ∀ a b, 1 ≤ a → 1 ≤ b → T (a * b) = T a * T b)
    {L : ℂ} (hL : Tendsto (fun N => ∑ r ∈ Icc 1 N, T r) atTop (𝓝 L)) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (cutDefectC T k) atTop (𝓝 ((1 - (k : ℂ) * T k) * L)) := by
  have hN : Tendsto (fun J : ℕ => k * J) atTop atTop := tendsto_id.const_mul_atTop' hk
  have h1 := hL.comp hN
  have h2 := hL.const_mul ((k : ℂ) * T k)
  have h3 := h1.sub h2
  have hval : L - (k : ℂ) * T k * L = (1 - (k : ℂ) * T k) * L := by ring
  rw [hval] at h3
  refine h3.congr fun J => ?_
  simp only [Function.comp, cutDefectC]
  rw [mul_assoc, mul_sum]
  congr 2
  refine sum_congr rfl fun j hj => ?_
  rw [hT k j hk (mem_Icc.mp hj).1]

/-- **A completely multiplicative kernel vector has vanishing `L`-value.** -/
theorem eq_zero_of_mul_kernel {T : ℕ → ℂ} (hT : ∀ a b, 1 ≤ a → 1 ≤ b → T (a * b) = T a * T b)
    {L : ℂ} (hL : Tendsto (fun N => ∑ r ∈ Icc 1 N, T r) atTop (𝓝 L))
    (hker : ∀ k : ℕ, 1 ≤ k → Tendsto (cutDefectC T k) atTop (𝓝 0)) : L = 0 := by
  by_contra hne
  have hval : ∀ k : ℕ, 1 ≤ k → (k : ℂ) * T k = 1 := by
    intro k hk
    have h := tendsto_nhds_unique (tendsto_cutDefectC_of_mul hT hL hk) (hker k hk)
    have h1 := (mul_eq_zero.mp h).resolve_right hne
    linear_combination -h1
  have hT1 : ∀ r : ℕ, 1 ≤ r → T r = ((1 / (r : ℝ) : ℝ) : ℂ) := by
    intro r hr
    have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have := hval r hr
    push_cast
    field_simp
    linear_combination this
  have hdiv : Tendsto (fun N : ℕ => ∑ r ∈ Icc 1 N, (1 / (r : ℝ))) atTop atTop := by
    have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
    refine h.congr fun N => ?_
    rw [sum_Icc_one_eq_sum_range]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hre : Tendsto (fun N : ℕ => ∑ r ∈ Icc 1 N, (1 / (r : ℝ))) atTop (𝓝 L.re) := by
    have h := Complex.continuous_re.tendsto L |>.comp hL
    refine h.congr fun N => ?_
    simp only [Function.comp, Complex.re_sum]
    refine sum_congr rfl fun r hr => ?_
    rw [hT1 r (mem_Icc.mp hr).1, Complex.ofReal_re]
  exact not_tendsto_nhds_of_tendsto_atTop hdiv _ hre

/-! ### Finite Hecke-invariant pieces of the kernel -/

/-- A commuting family on a finite-dimensional complex space has a common eigenvector. -/
theorem exists_common_eigenvector {F ι : Type*} [AddCommGroup F] [Module ℂ F]
    (f : ι → Module.End ℂ F) (hcomm : ∀ i j, Commute (f i) (f j)) (n : ℕ) :
    ∀ (V : Submodule ℂ F) [FiniteDimensional ℂ V], Module.finrank ℂ V = n → V ≠ ⊥ →
      (∀ i, ∀ v ∈ V, f i v ∈ V) → ∃ v ∈ V, v ≠ 0 ∧ ∀ i, ∃ μ : ℂ, f i v = μ • v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hn hne hinv
    by_cases hall : ∀ i, ∀ v ∈ V, ∃ μ : ℂ, f i v = μ • v
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact ⟨v, hv, hv0, fun i => hall i v hv⟩
    · push Not at hall
      obtain ⟨i, v₀, hv₀, hno⟩ := hall
      haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hne
      set g : Module.End ℂ V := (f i).restrict (hinv i) with hg
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue g
      obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
      set W : Submodule ℂ F := V ⊓ Module.End.eigenspace (f i) μ with hW
      have hle : W ≤ V := inf_le_left
      haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hle
      have hWne : W ≠ ⊥ := by
        intro hbot
        have hxmem : (x : F) ∈ W := by
          refine Submodule.mem_inf.mpr ⟨x.2, Module.End.mem_eigenspace_iff.mpr ?_⟩
          have := Module.End.mem_eigenspace_iff.mp hx.1
          exact congrArg Subtype.val this
        rw [hbot, Submodule.mem_bot] at hxmem
        exact hx.2 (Subtype.ext hxmem)
      have hlt : W < V := by
        refine lt_of_le_of_ne hle fun heq => ?_
        have hm : v₀ ∈ W := heq ▸ hv₀
        exact hno μ (Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hm).2)
      have hrank : Module.finrank ℂ W < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨v, hv, hv0, hμs⟩ := ih _ hrank W rfl hWne (fun j v hv => by
        obtain ⟨hvV, hvE⟩ := Submodule.mem_inf.mp hv
        refine Submodule.mem_inf.mpr ⟨hinv j v hvV, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have hE := Module.End.mem_eigenspace_iff.mp hvE
        have hc := congrArg (fun φ : Module.End ℂ F => φ v) (hcomm i j).eq
        simp only [Module.End.mul_apply] at hc
        rw [hc, hE, map_smul])
      exact ⟨v, hle hv, hv0, hμs⟩

/-- The dilation operator on functions. -/
def heckeOp (j : ℕ) : Module.End ℂ (ℕ → ℂ) := LinearMap.funLeft ℂ ℂ (j * ·)

/-- **A finite Hecke-invariant space contains a completely multiplicative vector.** So a finite piece
of the kernel stable under dilation contains a completely multiplicative kernel vector, whose
`L`-value vanishes: finite-dimensional dilation structure is a zero of an `L`-function. -/
theorem exists_mul_of_hecke_invariant (V : Submodule ℂ (ℕ → ℂ)) [FiniteDimensional ℂ V] (hV : V ≠ ⊥)
    (h0 : ∀ T ∈ V, T 0 = 0) (hinv : ∀ j : ℕ, 1 ≤ j → ∀ T ∈ V, (fun r => T (j * r)) ∈ V) :
    ∃ χ ∈ V, χ 1 = 1 ∧ ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → χ (a * b) = χ a * χ b := by
  have hcomm : ∀ i j : {j : ℕ // 1 ≤ j}, Commute (heckeOp i.1) (heckeOp j.1) := by
    intro i j
    ext T r
    simp only [Module.End.mul_apply, heckeOp, LinearMap.funLeft_apply]
    congr 1
    ring
  obtain ⟨T, hT, hT0, hμ⟩ := exists_common_eigenvector (fun j : {j : ℕ // 1 ≤ j} => heckeOp j.1) hcomm
    _ V rfl hV (fun j v hv => hinv j.1 j.2 v hv)
  choose μ hμ using hμ
  have hval : ∀ (a : ℕ) (ha : 1 ≤ a) (b : ℕ), T (a * b) = μ ⟨a, ha⟩ * T b := by
    intro a ha b
    have := congrFun (hμ ⟨a, ha⟩) b
    simpa [heckeOp, LinearMap.funLeft_apply] using this
  have hT1 : T 1 ≠ 0 := by
    intro h1
    apply hT0
    funext r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact h0 T hT
    · have := hval r hr 1
      rw [mul_one, h1, mul_zero] at this
      exact this
  refine ⟨(T 1)⁻¹ • T, V.smul_mem _ hT, ?_, fun a b ha hb => ?_⟩
  · simp [hT1]
  · have h1 := hval a ha b
    have h2 := hval a ha 1
    rw [mul_one] at h2
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1, h2]
    field_simp

end GaloisForLFunctions.RigidArithmeticOfCuts
