import GaloisForLFunctions.RHTower.SelbergMaassRationalCuspTransport
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Hecke operator `T_p` on `Γ₀(M)` Maass cusp forms

For a prime `p ∤ M` the representatives `α_∞ = (p 0; 0 1)` and `α_b = (1 b; 0 p)`,
`b mod p`, define `T_p f(z) = f(pz) + Σ_b f((z+b)/p)`.

For `γ = (A B; C D) ∈ Γ₀(M)` one has `α_i γ = γ'_i α_{σ(i)}` with `γ'_i ∈ Γ₀(M)`. Here `σ` is
the Möbius action of `(D B; C A)` on `P¹(𝔽_p) = Option (ZMod p)`, and there are four explicit
transfer matrices, one for each pair of cases `i, σ(i) ∈ {∞, b}`. In the case `∞ ↦ ∞`,
`C/p ≡ 0 (M)` because `p ∤ M`. The map `σ` is injective (the determinant is `1`), hence a
bijection of the finite set `P¹(𝔽_p)`. Therefore `T_p` preserves `Γ₀(M)`-invariance
(`heckeT_invariant`, `heckeH_mem`).

Each term `f(α_i z)` is a positive rational pullback. So it is again a `C²` Laplace
eigenfunction with the same eigenvalue, and it decays at every integral cusp. The Laplacian
`-y²(∂ₓ² + ∂ᵧ²)` is additive on `C²` functions (`laplacian_add`), so `T_p f` has the same
three properties (`heckeH_maass`).
-/

open Complex Matrix UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.Gamma0MaassHecke

noncomputable section

/-- The Hecke representatives on `ℂ`: `α_∞ z = p z` and `α_b z = (z + b)/p` for `b mod p`. -/
def heckeAct (p : ℕ) : Option (ZMod p) → ℂ → ℂ
  | none => fun z => p * z
  | some b => fun z => (z + (b.val : ℂ)) / p

/-- An `SL₂(ℤ)` matrix from its entries. -/
def mkSL (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) := ⟨!![a, b; c, d], by
  rw [Matrix.det_fin_two_of]; exact h⟩

theorem mkSL_smul (a b c d : ℤ) (h : a * d - b * c = 1) (z : ℍ) :
    ((mkSL a b c d h • z : ℍ) : ℂ) = (a * (z : ℂ) + b) / (c * z + d) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mkSL]

theorem mkSL_mem {M : ℕ} (a b c d : ℤ) (h : a * d - b * c = 1) (hc : (M : ℤ) ∣ c) :
    mkSL a b c d h ∈ CongruenceSubgroup.Gamma0 M := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp only [mkSL]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hc

/-- The Möbius action on `ℂ`. -/
def mobC (a b c d : ℤ) (w : ℂ) : ℂ := (a * w + b) / (c * w + d)

/-! ### The four transfer identities -/

variable {p : ℕ}

theorem rhs_form (A B C D b : ℤ) {z : ℂ} (hz : (C : ℂ) * z + D ≠ 0) :
    (mobC A B C D z + b) / p = ((A + b * C) * z + (B + b * D)) / (p * (C * z + D)) := by
  unfold mobC
  rw [div_add' _ _ _ hz, div_div, mul_comm ((C : ℂ) * z + D)]
  congr 1
  ring

theorem lhs_form_p (A B C D : ℤ) (z : ℂ) :
    p * mobC A B C D z = p * (A * z + B) / (C * z + D) := by
  unfold mobC; ring

/-- Case `b ↦ b''`: `α_b γ = γ' α_{b''}` with `γ' = (A+bC, k; pC, D - C b'')`,
`pk = B + bD - (A + bC) b''`. -/
theorem transfer_some_some (hp : (p : ℂ) ≠ 0) (A B C D b b'' k : ℤ)
    (hk : B + b * D - (A + b * C) * b'' = p * k) {z : ℂ} (hz : (C : ℂ) * z + D ≠ 0) :
    mobC (A + b * C) k (p * C) (D - C * b'') ((z + b'') / p) = (mobC A B C D z + b) / p := by
  rw [rhs_form A B C D b hz]
  unfold mobC
  have hkC : (B : ℂ) + b * D - (A + b * C) * b'' = p * k := by exact_mod_cast hk
  have hden : ((p * C : ℤ) : ℂ) * ((z + b'') / p) + ((D - C * b'' : ℤ) : ℂ) = C * z + D := by
    push_cast; field_simp; ring
  have hnum : (((A + b * C : ℤ) : ℂ)) * ((z + b'') / p) + (k : ℂ) =
      ((A + b * C) * z + (B + b * D)) / p := by
    rw [eq_div_iff hp]
    push_cast
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hp]
    linear_combination (-1 : ℂ) * hkC
  rw [hden, hnum, div_div]

/-- Case `b ↦ ∞` (`A + bC = pk'`): `γ' = (k', B + bD; C, pD)`. -/
theorem transfer_some_none (A B C D b k' : ℤ) (hk : A + b * C = p * k')
    {z : ℂ} (hz : (C : ℂ) * z + D ≠ 0) :
    mobC k' (B + b * D) C (p * D) (p * z) = (mobC A B C D z + b) / p := by
  rw [rhs_form A B C D b hz]
  unfold mobC
  have hkC : (A : ℂ) + b * C = p * k' := by exact_mod_cast hk
  have hden : (C : ℂ) * (p * z) + ((p * D : ℤ) : ℂ) = p * (C * z + D) := by push_cast; ring
  have hnum : (k' : ℂ) * (p * z) + ((B + b * D : ℤ) : ℂ) = (A + b * C) * z + (B + b * D) := by
    push_cast; linear_combination (-z) * hkC
  rw [hden, hnum]

/-- Case `∞ ↦ b''` (`D - C b'' = pk`): `γ' = (pA, B - A b''; C, k)`. -/
theorem transfer_none_some (hp : (p : ℂ) ≠ 0) (A B C D b'' k : ℤ) (hk : D - C * b'' = p * k)
    (z : ℂ) :
    mobC (p * A) (B - A * b'') C k ((z + b'') / p) = p * mobC A B C D z := by
  rw [lhs_form_p A B C D z]
  unfold mobC
  have hkC : (D : ℂ) - C * b'' = p * k := by exact_mod_cast hk
  have hden : (C : ℂ) * ((z + b'') / p) + (k : ℂ) = (C * z + D) / p := by
    rw [eq_div_iff hp, add_mul, mul_assoc, div_mul_cancel₀ _ hp]
    linear_combination (-1 : ℂ) * hkC
  have hnum : ((p * A : ℤ) : ℂ) * ((z + b'') / p) + ((B - A * b'' : ℤ) : ℂ) = A * z + B := by
    push_cast; field_simp; ring
  rw [hden, hnum, div_div_eq_mul_div, mul_comm]

/-- Case `∞ ↦ ∞` (`C = pk`): `γ' = (A, pB; k, D)`. -/
theorem transfer_none_none (A B C D k : ℤ) (hk : C = p * k) (z : ℂ) :
    mobC A (p * B) k D (p * z) = p * mobC A B C D z := by
  rw [lhs_form_p A B C D z]
  unfold mobC
  have hkC : (C : ℂ) = p * k := by exact_mod_cast hk
  have hden : (k : ℂ) * (p * z) + D = C * z + D := by rw [hkC]; ring
  rw [hden]
  push_cast
  ring

/-! ### The permutation of `P¹(𝔽_p)` -/

/-- `σ_γ` on `P¹(𝔽_p) = Option (ZMod p)`: the Möbius action of `(D B; C A)`. -/
def sigmaP (p : ℕ) [Fact p.Prime] (A B C D : ℤ) : Option (ZMod p) → Option (ZMod p)
  | none => if (C : ZMod p) = 0 then none else some ((D : ZMod p) / (C : ZMod p))
  | some b => if (A : ZMod p) + b * (C : ZMod p) = 0 then none
      else some (((B : ZMod p) + b * (D : ZMod p)) / ((A : ZMod p) + b * (C : ZMod p)))

variable (p) [hp : Fact p.Prime]

theorem sigmaP_injective (A B C D : ℤ) (hdet : A * D - B * C = 1) :
    Function.Injective (sigmaP p A B C D) := by
  have hd : (A : ZMod p) * D - B * C = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : ZMod p)) hdet
  have hA0 : ∀ a : ZMod p, (C : ZMod p) = 0 → (A : ZMod p) + a * C = 0 → False := by
    intro a hC hA
    rw [hC, mul_zero, add_zero] at hA
    rw [hA, hC] at hd; simp at hd
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some b =>
      exfalso
      by_cases h1 : (C : ZMod p) = 0
      · by_cases h2 : (A : ZMod p) + b * C = 0
        · exact hA0 b h1 h2
        · simp only [sigmaP] at hij; split_ifs at hij
      · by_cases h2 : (A : ZMod p) + b * C = 0
        · simp only [sigmaP] at hij; split_ifs at hij
        · simp only [sigmaP, h1, h2, if_false, Option.some.injEq] at hij
          rw [div_eq_div_iff h1 h2] at hij
          apply one_ne_zero (α := ZMod p)
          rw [← hd]; linear_combination hij
  | some a =>
    cases j with
    | none =>
      exfalso
      by_cases h1 : (C : ZMod p) = 0
      · by_cases h2 : (A : ZMod p) + a * C = 0
        · exact hA0 a h1 h2
        · simp only [sigmaP] at hij; split_ifs at hij
      · by_cases h2 : (A : ZMod p) + a * C = 0
        · simp only [sigmaP] at hij; split_ifs at hij
        · simp only [sigmaP, h1, h2, if_false, Option.some.injEq] at hij
          rw [div_eq_div_iff h2 h1] at hij
          apply one_ne_zero (α := ZMod p)
          rw [← hd]; linear_combination -hij
    | some b =>
      congr 1
      by_cases h1 : (A : ZMod p) + a * C = 0
      · by_cases h2 : (A : ZMod p) + b * C = 0
        · by_cases hC : (C : ZMod p) = 0
          · exact (hA0 a hC h1).elim
          · have : (a - b) * C = 0 := by linear_combination h1 - h2
            rcases mul_eq_zero.1 this with h | h
            · exact sub_eq_zero.1 h
            · exact absurd h hC
        · simp only [sigmaP] at hij; split_ifs at hij
      · by_cases h2 : (A : ZMod p) + b * C = 0
        · simp only [sigmaP] at hij; split_ifs at hij
        · simp only [sigmaP, h1, h2, if_false, Option.some.injEq] at hij
          rw [div_eq_div_iff h1 h2] at hij
          have : (a - b) * ((A : ZMod p) * D - B * C) = 0 := by linear_combination hij
          rw [hd, mul_one] at this
          exact sub_eq_zero.1 this

omit hp in
/-- The denominator `Cz + D` of an integral unimodular matrix does not vanish on `ℍ`. -/
theorem den_ne_zero (A B C D : ℤ) (hdet : A * D - B * C = 1) {z : ℂ} (hz : 0 < z.im) :
    (C : ℂ) * z + D ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.zero_im] at him
  rcases mul_eq_zero.1 him with h1 | h1
  · have hC : C = 0 := by exact_mod_cast h1
    subst hC
    have hre := congrArg Complex.re h
    simp at hre
    subst hre
    simp at hdet
  · linarith

theorem intCast_val (b : ZMod p) : ((b.val : ℤ) : ZMod p) = b := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem dvd_of_zmod {t : ℤ} (h : (t : ZMod p) = 0) : ∃ k : ℤ, t = p * k :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd t p).1 h

/-- For every Hecke index `i` there is `γ' ∈ Γ₀(M)` with `α_i γ = γ' α_{σ(i)}`. -/
theorem transfer_exists (M : ℕ) (hpM : Nat.Coprime p M) (A B C D : ℤ)
    (hdet : A * D - B * C = 1) (hMC : (M : ℤ) ∣ C) (i : Option (ZMod p)) {z : ℂ}
    (hz : 0 < z.im) :
    ∃ A' B' C' D' : ℤ, A' * D' - B' * C' = 1 ∧ (M : ℤ) ∣ C' ∧
      mobC A' B' C' D' (heckeAct p (sigmaP p A B C D i) z) =
        heckeAct p i (mobC A B C D z) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hden := den_ne_zero A B C D hdet hz
  cases i with
  | none =>
    by_cases hC : (C : ZMod p) = 0
    · obtain ⟨k, hk⟩ := dvd_of_zmod p hC
      have hMk : (M : ℤ) ∣ k := by
        have h1 : (M : ℤ) ∣ (p : ℤ) * k := hk ▸ hMC
        exact (Int.isCoprime_iff_gcd_eq_one.2 (by
          rw [Int.gcd_natCast_natCast]; exact hpM.symm)).dvd_of_dvd_mul_left h1
      refine ⟨A, p * B, k, D, ?_, hMk, ?_⟩
      · rw [← hdet, hk]; ring
      · simp only [sigmaP, hC, if_true, heckeAct]
        exact transfer_none_none A B C D k hk z
    · set b'' : ZMod p := (D : ZMod p) / (C : ZMod p)
      have hz0 : ((D - C * (b''.val : ℤ) : ℤ) : ZMod p) = 0 := by
        push_cast
        simp only [ZMod.natCast_zmod_val, b'']
        field_simp
        ring
      obtain ⟨k, hk⟩ := dvd_of_zmod p hz0
      refine ⟨p * A, B - A * b''.val, C, k, ?_, hMC, ?_⟩
      · linear_combination hdet - (A : ℤ) * hk
      · simp only [sigmaP, hC, if_false, heckeAct]
        have := transfer_none_some hp0 A B C D (b''.val : ℤ) k hk z
        simpa using this
  | some b =>
    by_cases hA : (A : ZMod p) + b * (C : ZMod p) = 0
    · have hz0 : ((A + (b.val : ℤ) * C : ℤ) : ZMod p) = 0 := by
        push_cast; simp only [ZMod.natCast_zmod_val]; exact hA
      obtain ⟨k', hk'⟩ := dvd_of_zmod p hz0
      refine ⟨k', B + b.val * D, C, p * D, ?_, hMC, ?_⟩
      · linear_combination hdet - (D : ℤ) * hk'
      · simp only [sigmaP, hA, if_true, heckeAct]
        have := transfer_some_none A B C D (b.val : ℤ) k' hk' hden
        simpa using this
    · set b'' : ZMod p := ((B : ZMod p) + b * (D : ZMod p)) / ((A : ZMod p) + b * (C : ZMod p))
      have hz0 : ((B + (b.val : ℤ) * D - (A + (b.val : ℤ) * C) * (b''.val : ℤ) : ℤ) : ZMod p)
          = 0 := by
        push_cast
        simp only [ZMod.natCast_zmod_val]
        simp only [b'']
        field_simp
        ring
      obtain ⟨k, hk⟩ := dvd_of_zmod p hz0
      refine ⟨A + b.val * C, k, p * C, D - C * b''.val, ?_, dvd_mul_of_dvd_right hMC _, ?_⟩
      · linear_combination hdet + (C : ℤ) * hk
      · simp only [sigmaP, hA, if_false, heckeAct]
        have := transfer_some_some hp0 A B C D (b.val : ℤ) (b''.val : ℤ) k hk hden
        simpa using this

omit hp in
/-- `Γ₀(M)`-invariance of a function on `ℂ`, tested on the upper half-plane. -/
def IsGamma0Inv (M : ℕ) (f : ℂ → ℂ) : Prop :=
  ∀ A B C D : ℤ, A * D - B * C = 1 → (M : ℤ) ∣ C → ∀ z : ℂ, 0 < z.im →
    f (mobC A B C D z) = f z

/-- The Hecke operator `T_p f(z) = f(pz) + Σ_{b mod p} f((z+b)/p)`. -/
def heckeT (f : ℂ → ℂ) (z : ℂ) : ℂ := ∑ i : Option (ZMod p), f (heckeAct p i z)

theorem heckeAct_im_pos (i : Option (ZMod p)) {z : ℂ} (hz : 0 < z.im) :
    0 < (heckeAct p i z).im := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  cases i with
  | none =>
    simp only [heckeAct]
    rw [show ((p : ℂ) * z).im = p * z.im by simp]
    positivity
  | some b =>
    simp only [heckeAct]
    rw [show ((z + (b.val : ℂ)) / p).im = z.im / p by
      rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]]
    positivity

/-- **`T_p` preserves `Γ₀(M)`-invariance** for primes `p ∤ M`: the representatives are
permuted by the Möbius action of `(D B; C A)` on `P¹(𝔽_p)`. -/
theorem heckeT_invariant (M : ℕ) (hpM : Nat.Coprime p M) {f : ℂ → ℂ}
    (hf : IsGamma0Inv M f) : IsGamma0Inv M (heckeT p f) := by
  intro A B C D hdet hMC z hz
  have hbij : Function.Bijective (sigmaP p A B C D) :=
    Finite.injective_iff_bijective.1 (sigmaP_injective p A B C D hdet)
  unfold heckeT
  calc ∑ i : Option (ZMod p), f (heckeAct p i (mobC A B C D z))
      = ∑ i : Option (ZMod p), f (heckeAct p (sigmaP p A B C D i) z) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        obtain ⟨A', B', C', D', hdet', hMC', heq⟩ := transfer_exists p M hpM A B C D hdet hMC i hz
        rw [← heq, hf A' B' C' D' hdet' hMC' _ (heckeAct_im_pos p _ hz)]
    _ = ∑ i : Option (ZMod p), f (heckeAct p i z) :=
        Equiv.sum_comp (Equiv.ofBijective _ hbij) (fun i => f (heckeAct p i z))

/-! ### Linearity of the Laplacian -/

section Laplacian

open GaloisForLFunctions.RHTower Filter
open scoped Topology

omit hp in
theorem second_fderiv_add {F G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F U) (hG : ContDiffOn ℝ 2 G U) {z : ℂ} (hz : z ∈ U) (v v' : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ (F + G) w v) z v' =
      fderiv ℝ (fun w => fderiv ℝ F w v) z v' + fderiv ℝ (fun w => fderiv ℝ G w v) z v' := by
  have hFd : ∀ w ∈ U, DifferentiableAt ℝ F w := fun w hw =>
    (hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hw)
  have hGd : ∀ w ∈ U, DifferentiableAt ℝ G w := fun w hw =>
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hw)
  have heq : (fun w => fderiv ℝ (F + G) w v) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ F w v) + (fun w => fderiv ℝ G w v) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [fderiv_add (hFd w hw) (hGd w hw)]
    rfl
  have hF1 : ContDiffOn ℝ 1 (fun w => fderiv ℝ F w v) U :=
    (hF.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hG1 : ContDiffOn ℝ 1 (fun w => fderiv ℝ G w v) U :=
    (hG.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have dF := (hF1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz)
  have dG := (hG1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz)
  rw [heq.fderiv_eq, fderiv_add dF dG]
  rfl

theorem isOpen_upper : IsOpen {w : ℂ | 0 < w.im} :=
  isOpen_lt continuous_const Complex.continuous_im

omit hp in
theorem laplacian_add {f g : ℍ → ℂ} (hf : IsRealSmoothUpperHalfPlane f)
    (hg : IsRealSmoothUpperHalfPlane g) (z : ℍ) :
    positiveHyperbolicLaplacian (f + g) z =
      positiveHyperbolicLaplacian f z + positiveHyperbolicLaplacian g z := by
  have hcomp : (f + g) ∘ UpperHalfPlane.ofComplex =
      f ∘ UpperHalfPlane.ofComplex + g ∘ UpperHalfPlane.ofComplex := rfl
  have hz : (z : ℂ) ∈ {w : ℂ | 0 < w.im} := z.2
  unfold positiveHyperbolicLaplacian
  rw [hcomp, second_fderiv_add isOpen_upper hf hg hz, second_fderiv_add isOpen_upper hf hg hz]
  ring

omit hp in
theorem isMaassEigenfunction_add {lam : ℝ} {f g : ℍ → ℂ} (hf : IsMaassEigenfunction lam f)
    (hg : IsMaassEigenfunction lam g) : IsMaassEigenfunction lam (f + g) := by
  refine ⟨hf.1.add hg.1, fun z => ?_⟩
  rw [laplacian_add hf.1 hg.1, hf.2 z, hg.2 z]
  simp only [Pi.add_apply]
  ring

omit hp in
theorem isMaassEigenfunction_zero (lam : ℝ) : IsMaassEigenfunction lam (0 : ℍ → ℂ) := by
  refine ⟨contDiffOn_const, fun z => ?_⟩
  have h0 : ((0 : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) = fun _ => (0 : ℂ) := rfl
  unfold positiveHyperbolicLaplacian
  rw [h0]
  simp

omit hp in
theorem isMaassEigenfunction_sum {ι : Type*} (s : Finset ι) {lam : ℝ} (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, IsMaassEigenfunction lam (f i)) :
    IsMaassEigenfunction lam (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isMaassEigenfunction_zero lam
  | insert a s ha ih =>
    have hfun : (fun z => ∑ i ∈ insert a s, f i z) = f a + fun z => ∑ i ∈ s, f i z := by
      funext z; simp [Finset.sum_insert ha]
    rw [hfun]
    exact isMaassEigenfunction_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

omit hp in
theorem isCuspidal_sum {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, IsCuspidalAtIntegralCusps (f i)) :
    IsCuspidalAtIntegralCusps (fun z => ∑ i ∈ s, f i z) := by
  intro σ
  have := tendsto_finsetSum s fun i hi => hf i hi σ
  rw [Finset.sum_const_zero] at this
  exact this

end Laplacian

/-! ### The Hecke operator on `Γ₀(M)` Maass cusp forms -/

section UpperHalf

open GaloisForLFunctions.RHTower

omit hp in
/-- The Hecke representatives `(p 0; 0 1)` and `(1 b; 0 p)` as rational matrices. -/
def alphaMat (p : ℕ) : Option (ZMod p) → Matrix (Fin 2) (Fin 2) ℚ
  | none => !![(p : ℚ), 0; 0, 1]
  | some b => !![1, (b.val : ℚ); 0, (p : ℚ)]

omit hp in
theorem alphaMat_det (i : Option (ZMod p)) : (alphaMat p i).det = p := by
  cases i <;> simp [alphaMat, Matrix.det_fin_two_of]

/-- The Hecke representatives in `GL₂(ℚ)`. -/
def alphaQ (i : Option (ZMod p)) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (alphaMat p i)
    (by rw [alphaMat_det]; exact_mod_cast hp.out.ne_zero)

theorem alphaQ_det_pos (i : Option (ZMod p)) :
    0 < ((alphaQ p i).map (algebraMap ℚ ℝ)).val.det := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  cases i <;> simp [alphaQ, alphaMat, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.det_fin_two, hp0]

theorem alphaQ_smul (i : Option (ZMod p)) (z : ℍ) :
    (((alphaQ p i).map (algebraMap ℚ ℝ) • z : ℍ) : ℂ) = heckeAct p i z := by
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det ((alphaQ p i).map (algebraMap ℚ ℝ)) : ℝˣ) : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact alphaQ_det_pos p i
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  cases i <;> simp [alphaQ, alphaMat, Matrix.GeneralLinearGroup.mkOfDetNeZero, UpperHalfPlane.num,
    UpperHalfPlane.denom, heckeAct, -ZMod.natCast_val]

/-- The Hecke operator `T_p f(z) = f(pz) + Σ_{b mod p} f((z+b)/p)` on functions on `ℍ`. -/
def heckeH (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  ∑ i : Option (ZMod p), f ((alphaQ p i).map (algebraMap ℚ ℝ) • z)

theorem heckeH_eq (f : ℍ → ℂ) (z : ℍ) :
    heckeH p f z = heckeT p (f ∘ UpperHalfPlane.ofComplex) z := by
  unfold heckeH heckeT
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp]
  rw [← alphaQ_smul p i z, UpperHalfPlane.ofComplex_apply]

omit hp in
theorem coe_integral_smul (σ : SL2Z) (z : ℍ) :
    ((integralSL2ToReal σ • z : ℍ) : ℂ) = mobC (σ 0 0) (σ 0 1) (σ 1 0) (σ 1 1) z := by
  change ((σ • z : ℍ) : ℂ) = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mobC]

omit hp in
/-- A `Γ₀(M)`-invariant function on `ℍ` gives a `Γ₀(M)`-invariant function on `ℂ`. -/
theorem gamma0Inv_of_mem {M : ℕ} {f : ℍ → ℂ}
    (hf : f ∈ upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma0 M))) :
    IsGamma0Inv M (f ∘ UpperHalfPlane.ofComplex) := by
  intro A B C D hdet hMC z hz
  have hmem : integralSL2ToReal (mkSL A B C D hdet) ∈
      realImage (CongruenceSubgroup.Gamma0 M) :=
    Subgroup.mem_map_of_mem _ (mkSL_mem A B C D hdet hMC)
  have key := hf ⟨_, hmem⟩ (UpperHalfPlane.ofComplex z)
  have hz' : ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hcoe : ((integralSL2ToReal (mkSL A B C D hdet) • UpperHalfPlane.ofComplex z : ℍ) : ℂ) =
      mobC A B C D z := by
    change ((mkSL A B C D hdet • UpperHalfPlane.ofComplex z : ℍ) : ℂ) = _
    rw [mkSL_smul, hz']
    rfl
  simp only [Function.comp]
  rw [← hcoe, UpperHalfPlane.ofComplex_apply]
  exact key

/-- **`T_p` maps `Γ₀(M)`-invariant functions to `Γ₀(M)`-invariant functions** (`p ∤ M`). -/
theorem heckeH_mem {M : ℕ} (hpM : Nat.Coprime p M) {f : ℍ → ℂ}
    (hf : f ∈ upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma0 M))) :
    heckeH p f ∈ upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma0 M)) := by
  intro γ z
  obtain ⟨σ, hσ, hγ⟩ := Subgroup.mem_map.1 γ.2
  rw [heckeH_eq, heckeH_eq, ← hγ, coe_integral_smul]
  have hdet : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rwa [Matrix.det_fin_two] at this
  have hMC : (M : ℤ) ∣ σ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hσ)
  exact heckeT_invariant p M hpM (gamma0Inv_of_mem hf) _ _ _ _ hdet hMC z z.2

/-- **The Hecke operator on Maass cusp forms.** For a prime `p ∤ M` and a Maass cusp form `f`
on `Γ₀(M)` with eigenvalue `λ`, `T_p f` is `Γ₀(M)`-invariant, a `C²` eigenfunction of the
Laplacian with the same eigenvalue, and decays at every integral cusp. -/
theorem heckeH_maass {M : ℕ} (hpM : Nat.Coprime p M) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 M)) lam) :
    heckeH p f.1.1 ∈ upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma0 M)) ∧
      IsMaassEigenfunction lam (heckeH p f.1.1) ∧ IsCuspidalAtIntegralCusps (heckeH p f.1.1) := by
  have hterm : ∀ i : Option (ZMod p),
      IsMaassEigenfunction lam (fun w => f.1.1 ((alphaQ p i).map (algebraMap ℚ ℝ) • w)) ∧
        IsCuspidalAtIntegralCusps (fun w => f.1.1 ((alphaQ p i).map (algebraMap ℚ ℝ) • w)) :=
    fun i => rationalGL_maass_eigenfunction_cuspidal_pullback (alphaQ p i) (alphaQ_det_pos p i)
      lam f.1.1 f.2.2.1 f.2.2.2
  refine ⟨heckeH_mem p hpM f.1.2, ?_, ?_⟩
  · exact isMaassEigenfunction_sum Finset.univ _ fun i _ => (hterm i).1
  · exact isCuspidal_sum Finset.univ _ fun i _ => (hterm i).2

end UpperHalf

end

end GaloisForLFunctions.RHTower.Gamma0MaassHecke
