import GaloisForLFunctions.HTGeometry.HLSEvenAlgebra
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# ℤ₂-graded symmetries of the Coleman--Mandula algebra

`HLSGradedSymmetry` packages a Lie superalgebra `𝔤 = 𝔤₀ ⊕ 𝔤₁` whose even part is the
explicit Coleman--Mandula algebra `HLSEven B` of `HLSEvenAlgebra`, together with

* the real form (an antilinear involution `★` of `𝔤`), and
* the physical positivity input: a state functional `ω` whose four-momentum lies in the
  open forward cone and for which `ω({Q, Q★}) > 0` whenever `Q ≠ 0`.

These are exactly the hypotheses of the Haag--Łopuszański--Sohnius theorem after the
Coleman--Mandula analysis has fixed the even part.  No further assumption is made about
the odd part: it is an arbitrary finite-dimensional complex vector space.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

variable {B : Type*} [LieRing B] [LieAlgebra ℂ B]

/-- A real form of the internal symmetry algebra: an antilinear Lie involution. -/
structure HLSInternalRealForm (B : Type*) [LieRing B] [LieAlgebra ℂ B] where
  /-- The antilinear conjugation. -/
  conj : B →ₛₗ[starRingEnd ℂ] B
  /-- It is an involution. -/
  conj_conj : ∀ b, conj (conj b) = b
  /-- It is a Lie algebra map. -/
  conj_lie : ∀ b c, conj ⁅b, c⁆ = ⁅conj b, conj c⁆

/-- The real-form conjugation of `𝔤₀`: it exchanges the two `𝔰𝔩₂` factors (with entrywise
complex conjugation), conjugate-transposes the translations, and applies the internal
conjugation. -/
def hlsEvenConj (ι : HLSInternalRealForm B) (X : HLSEven B) : HLSEven B :=
  (star X.2.1, star X.1, (X.2.2.1)ᴴ, ι.conj X.2.2.2)

theorem hlsSl2Br_star (x y : HLSSl2) : hlsSl2Br (star x) (star y) = star (hlsSl2Br x y) := by
  funext i
  fin_cases i <;>
    simp [hlsSl2Br, Pi.star_apply, star_sub, star_mul']

theorem hlsSl2Mat_star (x : HLSSl2) : hlsSl2Mat (star x) = (hlsSl2Mat x)ᵀᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsSl2Mat, Matrix.conjTranspose_apply, Pi.star_apply]

@[simp] theorem hlsEvenConj_conj (ι : HLSInternalRealForm B) (X : HLSEven B) :
    hlsEvenConj ι (hlsEvenConj ι X) = X := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact star_star _
  · exact star_star _
  · exact Matrix.conjTranspose_conjTranspose _
  · exact ι.conj_conj _

theorem hlsEvenConj_add (ι : HLSInternalRealForm B) (X Y : HLSEven B) :
    hlsEvenConj ι (X + Y) = hlsEvenConj ι X + hlsEvenConj ι Y := by
  refine Prod.ext (star_add _ _) (Prod.ext (star_add _ _) (Prod.ext ?_ ?_))
  · exact Matrix.conjTranspose_add _ _
  · exact map_add _ _ _

theorem hlsEvenConj_smul (ι : HLSInternalRealForm B) (c : ℂ) (X : HLSEven B) :
    hlsEvenConj ι (c • X) = (starRingEnd ℂ) c • hlsEvenConj ι X := by
  refine Prod.ext (star_smul _ _) (Prod.ext (star_smul _ _) (Prod.ext ?_ ?_))
  · exact Matrix.conjTranspose_smul _ _
  · exact map_smulₛₗ ι.conj c _

theorem hlsEvenConj_br (ι : HLSInternalRealForm B) (X Y : HLSEven B) :
    hlsEvenConj ι (hlsEvenBr X Y) = hlsEvenBr (hlsEvenConj ι X) (hlsEvenConj ι Y) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact (hlsSl2Br_star _ _).symm
  · exact (hlsSl2Br_star _ _).symm
  · show (hlsLorAct X.1 X.2.1 Y.2.2.1 - hlsLorAct Y.1 Y.2.1 X.2.2.1)ᴴ
      = hlsLorAct (star X.2.1) (star X.1) (Y.2.2.1)ᴴ
        - hlsLorAct (star Y.2.1) (star Y.1) (X.2.2.1)ᴴ
    have key : ∀ (x x' : HLSSl2) (P : Matrix (Fin 2) (Fin 2) ℂ),
        (hlsLorAct x x' P)ᴴ = hlsLorAct (star x') (star x) Pᴴ := by
      intro x x' P
      simp only [hlsLorAct, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
        hlsSl2Mat_star, Matrix.transpose_conjTranspose]
      exact add_comm _ _
    rw [Matrix.conjTranspose_sub, key, key]
  · show ι.conj ⁅X.2.2.2, Y.2.2.2⁆ = ⁅ι.conj X.2.2.2, ι.conj Y.2.2.2⁆
    exact ι.conj_lie _ _

@[simp] theorem hlsEvenConj_lorL (ι : HLSInternalRealForm B) (x : HLSSl2) :
    hlsEvenConj ι (hlsLorL x) = hlsLorR (star x) := by
  simp [hlsEvenConj, hlsLorL, hlsLorR]

@[simp] theorem hlsEvenConj_lorR (ι : HLSInternalRealForm B) (x : HLSSl2) :
    hlsEvenConj ι (hlsLorR x) = hlsLorL (star x) := by
  simp [hlsEvenConj, hlsLorL, hlsLorR]

@[simp] theorem hlsEvenConj_mom (ι : HLSInternalRealForm B) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsEvenConj ι (hlsMom P) = hlsMom (B := B) Pᴴ := by
  simp [hlsEvenConj, hlsMom]

@[simp] theorem hlsEvenConj_int (ι : HLSInternalRealForm B) (b : B) :
    hlsEvenConj ι (hlsInt b) = hlsInt (ι.conj b) := by
  simp [hlsEvenConj, hlsInt]

@[simp] theorem hlsSl2H_star : star hlsSl2H = hlsSl2H := by
  funext i; fin_cases i <;> simp [hlsSl2H, Pi.star_apply]


@[simp] theorem hlsLorL_smul (c : ℂ) (x : HLSSl2) :
    (hlsLorL (c • x) : HLSEven B) = c • hlsLorL x := by
  simp [hlsLorL, Prod.smul_mk]

@[simp] theorem hlsLorR_smul (c : ℂ) (x : HLSSl2) :
    (hlsLorR (c • x) : HLSEven B) = c • hlsLorR x := by
  simp [hlsLorR, Prod.smul_mk]

theorem hlsEvenBr_lorL_lorL (x y : HLSSl2) :
    hlsEvenBr (hlsLorL x) (hlsLorL y : HLSEven B) = hlsLorL (hlsSl2Br x y) := by
  rw [hlsEvenBr_lorL]; simp [hlsLorL]

theorem hlsEvenBr_lorR_lorR (x y : HLSSl2) :
    hlsEvenBr (hlsLorR x) (hlsLorR y : HLSEven B) = hlsLorR (hlsSl2Br x y) := by
  rw [hlsEvenBr_lorR]; simp [hlsLorR]

theorem hlsEvenBr_lorL_lorR (x y : HLSSl2) :
    hlsEvenBr (hlsLorL x) (hlsLorR y : HLSEven B) = 0 := by
  rw [hlsEvenBr_lorL]; simp [hlsLorR]

theorem hlsEvenBr_lorL_mom (x : HLSSl2) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsEvenBr (hlsLorL x) (hlsMom P : HLSEven B) = hlsMom (hlsSl2Mat x * P) := by
  rw [hlsEvenBr_lorL]; simp [hlsMom]

theorem hlsEvenBr_lorR_mom (x : HLSSl2) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsEvenBr (hlsLorR x) (hlsMom P : HLSEven B) = hlsMom (P * (hlsSl2Mat x)ᵀ) := by
  rw [hlsEvenBr_lorR]; simp [hlsMom]

theorem hlsEvenBr_lorL_int (x : HLSSl2) (b : B) :
    hlsEvenBr (hlsLorL x) (hlsInt b : HLSEven B) = 0 := by
  rw [hlsEvenBr_lorL]; simp [hlsInt]

theorem hlsEvenBr_lorR_int (x : HLSSl2) (b : B) :
    hlsEvenBr (hlsLorR x) (hlsInt b : HLSEven B) = 0 := by
  rw [hlsEvenBr_lorR]; simp [hlsInt]

theorem hlsEvenBr_mom_mom (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsEvenBr (hlsMom P) (hlsMom Q : HLSEven B) = 0 := by
  simp [hlsEvenBr, hlsMom]

theorem hlsEvenBr_mom_int (P : Matrix (Fin 2) (Fin 2) ℂ) (b : B) :
    hlsEvenBr (hlsMom P) (hlsInt b : HLSEven B) = 0 := by
  simp [hlsEvenBr, hlsMom, hlsInt]

theorem hlsEvenBr_int_int (b c : B) :
    hlsEvenBr (hlsInt b) (hlsInt c : HLSEven B) = hlsInt ⁅b, c⁆ := by
  simp [hlsEvenBr, hlsInt]

/-- **Generalized eigenvalues add along an equivariant bilinear map.**
If `c ∘ f = f ∘ (a ⊗ 1) + f ∘ (1 ⊗ b)` and `x`, `y` are generalized eigenvectors of `a`, `b`
for `α`, `β`, then `f x y` is a generalized eigenvector of `c` for `α + β`. -/
theorem hlsGenEigen_bilinear {M N P : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] [AddCommGroup P] [Module ℂ P]
    (f : M →ₗ[ℂ] N →ₗ[ℂ] P) (a : Module.End ℂ M) (b : Module.End ℂ N) (c : Module.End ℂ P)
    (α β : ℂ) (hleib : ∀ x y, c (f x y) = f (a x) y + f x (b y)) :
    ∀ (i j : ℕ) (x : M) (y : N),
      ((a - α • (1 : Module.End ℂ M)) ^ i) x = 0 →
      ((b - β • (1 : Module.End ℂ N)) ^ j) y = 0 →
      (((c - (α + β) • (1 : Module.End ℂ P)) ^ (i + j)) (f x y)) = 0 := by
  set A : Module.End ℂ M := a - α • (1 : Module.End ℂ M) with hA
  set Bo : Module.End ℂ N := b - β • (1 : Module.End ℂ N) with hBo
  set C : Module.End ℂ P := c - (α + β) • (1 : Module.End ℂ P) with hC
  have step : ∀ x y, C (f x y) = f (A x) y + f x (Bo y) := by
    intro x y
    have h := hleib x y
    simp only [hA, hBo, hC, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, LinearMap.add_apply, add_smul]
    rw [h]
    abel
  intro i
  induction i with
  | zero =>
      intro j x y hx _
      simp only [pow_zero, Module.End.one_apply] at hx
      subst hx
      simp
  | succ i ih =>
      intro j
      induction j with
      | zero =>
          intro x y _ hy
          simp only [pow_zero, Module.End.one_apply] at hy
          subst hy
          simp
      | succ j ihj =>
          intro x y hx hy
          have hxA : (A ^ i) (A x) = 0 := by
            rw [← Module.End.mul_apply, ← pow_succ]
            exact hx
          have hyB : (Bo ^ j) (Bo y) = 0 := by
            rw [← Module.End.mul_apply, ← pow_succ]
            exact hy
          have e1 : (C ^ (i + (j + 1))) (f (A x) y) = 0 := ih (j + 1) (A x) y hxA hy
          have e2 : (C ^ (i + 1 + j)) (f x (Bo y)) = 0 := ihj x (Bo y) hx hyB
          have hidx1 : i + (j + 1) = i + 1 + j := by omega
          have hidx2 : i + 1 + (j + 1) = (i + 1 + j) + 1 := by omega
          rw [hidx2, pow_succ, Module.End.mul_apply, step, map_add]
          rw [hidx1] at e1
          rw [e1, e2, add_zero]

/-- **The Haag--Łopuszański--Sohnius input.**  A `ℤ₂`-graded Lie algebra whose even part is
the Coleman--Mandula algebra `HLSEven B`, whose odd part is the finite-dimensional complex
vector space `V`, equipped with a real form and the physical positivity of the odd sector. -/
structure HLSGradedSymmetry (B : Type*) [LieRing B] [LieAlgebra ℂ B]
    (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- Real form of the internal symmetry algebra. -/
  internal : HLSInternalRealForm B
  /-- Action of the even part on the odd part (the even--odd bracket). -/
  act : HLSEven B →ₗ[ℂ] V →ₗ[ℂ] V
  /-- The odd--odd anticommutator. -/
  br : V →ₗ[ℂ] V →ₗ[ℂ] HLSEven B
  /-- The anticommutator of two odd elements is symmetric. -/
  br_symm : ∀ u v, br u v = br v u
  /-- Graded Jacobi identity for two even and one odd element. -/
  act_lie : ∀ X Y v, act (hlsEvenBr X Y) v = act X (act Y v) - act Y (act X v)
  /-- Graded Jacobi identity for one even and two odd elements. -/
  act_br : ∀ X u v, hlsEvenBr X (br u v) = br (act X u) v + br u (act X v)
  /-- Graded Jacobi identity for three odd elements. -/
  jacobi : ∀ u v w, act (br u v) w + act (br v w) u + act (br w u) v = 0
  /-- The antilinear involution cutting out the real form on the odd part. -/
  oddConj : V →ₛₗ[starRingEnd ℂ] V
  /-- It is an involution. -/
  oddConj_conj : ∀ v, oddConj (oddConj v) = v
  /-- It is compatible with the even action. -/
  oddConj_act : ∀ X v, oddConj (act X v) = act (hlsEvenConj internal X) (oddConj v)
  /-- It is compatible with the anticommutator. -/
  oddConj_br : ∀ u v, br (oddConj u) (oddConj v) = hlsEvenConj internal (br u v)
  /-- A physical state functional on the even algebra. -/
  state : HLSEven B →ₗ[ℂ] ℂ
  /-- The state functional is real on the real form. -/
  state_conj : ∀ X, state (hlsEvenConj internal X) = starRingEnd ℂ (state X)
  /-- Spectrum condition: the state's four-momentum lies in the open forward cone. -/
  state_mom_posDef :
    (Matrix.of fun a b => state (hlsMom (B := B) (Matrix.single a b (1 : ℂ)))).PosDef
  /-- Positivity of the odd sector: `⟨{Q, Q★}⟩ > 0` for every nonzero odd `Q`. -/
  state_positive : ∀ v : V, v ≠ 0 → 0 < (state (br v (oddConj v))).re

namespace HLSGradedSymmetry

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (S : HLSGradedSymmetry B V)

/-- Undotted Lorentz action on the odd part. -/
def LL (x : HLSSl2) : Module.End ℂ V := S.act (hlsLorL x)

/-- Dotted Lorentz action on the odd part. -/
def RR (x : HLSSl2) : Module.End ℂ V := S.act (hlsLorR x)

theorem LL_smul (c : ℂ) (x : HLSSl2) : S.LL (c • x) = c • S.LL x := by
  simp [LL, map_smul]

theorem RR_smul (c : ℂ) (x : HLSSl2) : S.RR (c • x) = c • S.RR x := by
  simp [RR, map_smul]

theorem LL_comm (x y : HLSSl2) : S.LL x * S.LL y - S.LL y * S.LL x = S.LL (hlsSl2Br x y) := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LL]
  rw [← S.act_lie, hlsEvenBr_lorL_lorL]

theorem RR_comm (x y : HLSSl2) : S.RR x * S.RR y - S.RR y * S.RR x = S.RR (hlsSl2Br x y) := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, RR]
  rw [← S.act_lie, hlsEvenBr_lorR_lorR]

theorem LL_RR_commute (x y : HLSSl2) : S.LL x * S.RR y = S.RR y * S.LL x := by
  ext v
  have h := S.act_lie (hlsLorL x) (hlsLorR y) v
  rw [hlsEvenBr_lorL_lorR, map_zero] at h
  simp only [Module.End.mul_apply, LL, RR]
  have h0 : (0 : V →ₗ[ℂ] V) v = 0 := rfl
  rw [h0] at h
  exact sub_eq_zero.mp h.symm

/-- Undotted Cartan generator acting on the odd part. -/
abbrev hL : Module.End ℂ V := S.LL hlsSl2H

/-- Undotted raising generator acting on the odd part. -/
abbrev eL : Module.End ℂ V := S.LL hlsSl2E

/-- Undotted lowering generator acting on the odd part. -/
abbrev fL : Module.End ℂ V := S.LL hlsSl2F

/-- Dotted Cartan generator acting on the odd part. -/
abbrev hR : Module.End ℂ V := S.RR hlsSl2H

/-- Dotted raising generator acting on the odd part. -/
abbrev eR : Module.End ℂ V := S.RR hlsSl2E

/-- Dotted lowering generator acting on the odd part. -/
abbrev fR : Module.End ℂ V := S.RR hlsSl2F

theorem hL_eL : S.hL * S.eL - S.eL * S.hL = (2 : ℂ) • S.eL := by
  rw [LL_comm, hlsSl2Br_h_e, LL_smul]

theorem hL_fL : S.hL * S.fL - S.fL * S.hL = (-2 : ℂ) • S.fL := by
  rw [LL_comm, hlsSl2Br_h_f, LL_smul]

theorem eL_fL : S.eL * S.fL - S.fL * S.eL = S.hL := by
  rw [LL_comm, hlsSl2Br_e_f]

theorem hR_eR : S.hR * S.eR - S.eR * S.hR = (2 : ℂ) • S.eR := by
  rw [RR_comm, hlsSl2Br_h_e, RR_smul]

theorem hR_fR : S.hR * S.fR - S.fR * S.hR = (-2 : ℂ) • S.fR := by
  rw [RR_comm, hlsSl2Br_h_f, RR_smul]

theorem eR_fR : S.eR * S.fR - S.fR * S.eR = S.hR := by
  rw [RR_comm, hlsSl2Br_e_f]


theorem oddConj_LL (x : HLSSl2) (v : V) : S.oddConj (S.LL x v) = S.RR (star x) (S.oddConj v) := by
  simpa [LL, RR] using S.oddConj_act (hlsLorL x) v

theorem oddConj_RR (x : HLSSl2) (v : V) : S.oddConj (S.RR x v) = S.LL (star x) (S.oddConj v) := by
  simpa [LL, RR] using S.oddConj_act (hlsLorR x) v

theorem oddConj_hL (v : V) : S.oddConj (S.hL v) = S.hR (S.oddConj v) := by
  simpa using S.oddConj_LL hlsSl2H v

theorem oddConj_hR (v : V) : S.oddConj (S.hR v) = S.hL (S.oddConj v) := by
  simpa using S.oddConj_RR hlsSl2H v

theorem oddConj_eL (v : V) : S.oddConj (S.eL v) = S.eR (S.oddConj v) := by
  have hE : star hlsSl2E = hlsSl2E := by funext i; fin_cases i <;> simp [hlsSl2E, Pi.star_apply]
  simpa [hE] using S.oddConj_LL hlsSl2E v

theorem oddConj_fL (v : V) : S.oddConj (S.fL v) = S.fR (S.oddConj v) := by
  have hF : star hlsSl2F = hlsSl2F := by funext i; fin_cases i <;> simp [hlsSl2F, Pi.star_apply]
  simpa [hF] using S.oddConj_LL hlsSl2F v

theorem oddConj_eR (v : V) : S.oddConj (S.eR v) = S.eL (S.oddConj v) := by
  have hE : star hlsSl2E = hlsSl2E := by funext i; fin_cases i <;> simp [hlsSl2E, Pi.star_apply]
  simpa [hE] using S.oddConj_RR hlsSl2E v

theorem oddConj_fR (v : V) : S.oddConj (S.fR v) = S.fL (S.oddConj v) := by
  have hF : star hlsSl2F = hlsSl2F := by funext i; fin_cases i <;> simp [hlsSl2F, Pi.star_apply]
  simpa [hF] using S.oddConj_RR hlsSl2F v

/-- The undotted Cartan acts on the odd--odd bracket by the Leibniz rule. -/
theorem adL_br (u v : V) :
    hlsEvenAdL B (S.br u v) = S.br (S.hL u) v + S.br u (S.hL v) :=
  S.act_br (hlsLorL hlsSl2H) u v

/-- The dotted Cartan acts on the odd--odd bracket by the Leibniz rule. -/
theorem adR_br (u v : V) :
    hlsEvenAdR B (S.br u v) = S.br (S.hR u) v + S.br u (S.hR v) :=
  S.act_br (hlsLorR hlsSl2H) u v

/-- The undotted Cartan acts on the even--odd bracket by the Leibniz rule. -/
theorem hL_act (X : HLSEven B) (v : V) :
    S.hL (S.act X v) = S.act (hlsEvenAdL B X) v + S.act X (S.hL v) := by
  have h := S.act_lie (hlsLorL hlsSl2H) X v
  have : hlsEvenAdL B X = hlsEvenBr (hlsLorL hlsSl2H) X := rfl
  rw [this]
  rw [h]
  simp [hL, LL]

/-- The dotted Cartan acts on the even--odd bracket by the Leibniz rule. -/
theorem hR_act (X : HLSEven B) (v : V) :
    S.hR (S.act X v) = S.act (hlsEvenAdR B X) v + S.act X (S.hR v) := by
  have h := S.act_lie (hlsLorR hlsSl2H) X v
  have : hlsEvenAdR B X = hlsEvenBr (hlsLorR hlsSl2H) X := rfl
  rw [this]
  rw [h]
  simp [hR, RR]

/-- Positivity forces `{Q, Q★} ≠ 0` for every nonzero odd `Q`. -/
theorem br_oddConj_ne_zero {v : V} (hv : v ≠ 0) : S.br v (S.oddConj v) ≠ 0 := by
  intro h
  have := S.state_positive v hv
  rw [h, map_zero] at this
  simp at this

end HLSGradedSymmetry

end GaloisForLFunctions.HTGeometry
