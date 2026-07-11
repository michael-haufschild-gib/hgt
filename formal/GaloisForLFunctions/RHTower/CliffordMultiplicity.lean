import GaloisForLFunctions.RHTower.RHLadderTheory
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Clifford multiplicity divisibility and the Clifford reading of every rung

A finite-dimensional complex space carrying `2k` anticommuting complex structures
(`Jᵢ² = -1`, `JᵢJⱼ = -JⱼJᵢ`) — equivalently a module over `Cl_{2k}(ℂ) ≅ M_{2^k}(ℂ)` — has
dimension divisible by `2^k`: the `i`-eigenspace of `J₁` is half the space (`J₂` swaps the two
`J₁`-eigenspaces), and it carries the `2k - 2` anticommuting structures `J₂Jⱼ` (`j ≥ 3`), so
induction halves the space `k` times.  If the structures moreover commute with an endomorphism
`K`, they preserve every generalized eigenspace of `K`, so **every algebraic multiplicity of
`K` is divisible by `2^k`** — at every eigenvalue, with no constraint on the spectrum's
location.  This is the level-`k` Clifford extension of the Kramers parity mechanism: one
anticommuting pair forces evenness, `k` pairs force `2^k`-divisibility, and the dyadic tower of
demands matches the Clifford periodicity `Cl_{n+2} ≅ Cl_n ⊗ M_2`.

Applied to the multiplicity-parity ladder: `RHLadder k` holds iff every right-half ξ-zero
order is the algebraic multiplicity, at that zero, of an endomorphism commuting with `2k`
anticommuting complex structures (`rhLadder_iff_cliffordModel`).  Forward is the scalar model
on a doubled space; backward is the divisibility mechanism.  Levels are coherent: forgetting
generators restricts a level-`k` model to every lower level, matching the downward nesting of
the ladder, and RH itself is the existence of models at every level — equivalently at
unboundedly many levels.
-/

open Complex Module

namespace RHTower

section Mechanism

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

private theorem end_sq_apply {A : Module.End ℂ V} (h : A * A = -1) (x : V) : A (A x) = -x := by
  have hx := DFunLike.congr_fun h x
  simpa [Module.End.mul_apply] using hx

private theorem end_anticomm_apply {A B : Module.End ℂ V} (h : A * B = -(B * A)) (x : V) :
    A (B x) = -(B (A x)) := by
  have hx := DFunLike.congr_fun h x
  simpa [Module.End.mul_apply] using hx

/-- **Clifford dimension divisibility.**  A finite-dimensional complex space carrying `2k`
anticommuting complex structures has dimension divisible by `2^k`. -/
private theorem pow_dvd_finrank_aux (k : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (J : Fin (2 * k) → Module.End ℂ V),
      (∀ i, J i * J i = -1) → (∀ i j, i ≠ j → J i * J j = -(J j * J i)) →
      2 ^ k ∣ finrank ℂ V := by
  induction k with
  | zero =>
    intro V _ _ _ J _ _
    simp
  | succ k ih =>
    intro V _ _ _ J hsq hanti
    set i₀ : Fin (2 * (k + 1)) := ⟨0, by omega⟩ with hi₀
    set i₁ : Fin (2 * (k + 1)) := ⟨1, by omega⟩ with hi₁
    set A := J i₀ with hA
    set B := J i₁ with hB
    have hne01 : i₀ ≠ i₁ := by simp [hi₀, hi₁]
    have hA2x : ∀ x : V, A (A x) = -x := end_sq_apply (hsq i₀)
    have hB2x : ∀ x : V, B (B x) = -x := end_sq_apply (hsq i₁)
    have hABx : ∀ x : V, A (B x) = -(B (A x)) := end_anticomm_apply (hanti i₀ i₁ hne01)
    set Wp : Submodule ℂ V := LinearMap.ker (A - Complex.I • 1) with hWp
    set Wm : Submodule ℂ V := LinearMap.ker (A + Complex.I • 1) with hWm
    have hmemp : ∀ x : V, x ∈ Wp ↔ A x = Complex.I • x := by
      intro x
      rw [hWp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, sub_eq_zero]
    have hmemm : ∀ x : V, x ∈ Wm ↔ A x = -(Complex.I • x) := by
      intro x
      rw [hWm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, add_eq_zero_iff_eq_neg]
    -- the two eigenspaces intersect trivially and span
    have hinf : Wp ⊓ Wm = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf, hmemp, hmemm] at hx
      have h2 : (2 * Complex.I) • x = 0 := by
        have := hx.1.symm.trans hx.2
        rw [eq_neg_iff_add_eq_zero] at this
        calc (2 * Complex.I) • x = Complex.I • x + Complex.I • x := by module
          _ = 0 := this
      have h2ne : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
      simpa [Submodule.mem_bot] using (smul_eq_zero.mp h2).resolve_left h2ne
    have hup : ∀ x : V, (x - Complex.I • A x) ∈ Wp := by
      intro x
      rw [hmemp, map_sub, map_smul, hA2x, smul_sub, smul_smul, Complex.I_mul_I]
      module
    have hum : ∀ x : V, (x + Complex.I • A x) ∈ Wm := by
      intro x
      rw [hmemm, map_add, map_smul, hA2x, smul_add, smul_smul, Complex.I_mul_I]
      module
    have hsup : Wp ⊔ Wm = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      exact ⟨(1 / 2 : ℂ) • (x - Complex.I • A x), Submodule.smul_mem _ _ (hup x),
        (1 / 2 : ℂ) • (x + Complex.I • A x), Submodule.smul_mem _ _ (hum x), by module⟩
    -- `B` exchanges the eigenspaces, so they have equal rank
    have hBpm : ∀ x ∈ Wp, B x ∈ Wm := by
      intro x hx
      rw [hmemp] at hx
      rw [hmemm, hABx, hx, map_smul]
    have hBmp : ∀ x ∈ Wm, (-B) x ∈ Wp := by
      intro x hx
      rw [hmemm] at hx
      rw [hmemp, LinearMap.neg_apply, map_neg, hABx, hx]
      simp [map_smul]
    have hcomp₁ : ∀ x : V, B ((-B) x) = x := by
      intro x
      rw [LinearMap.neg_apply, map_neg, hB2x, neg_neg]
    have hcomp₂ : ∀ x : V, (-B) (B x) = x := by
      intro x
      rw [LinearMap.neg_apply, hB2x, neg_neg]
    let e : ↥Wp ≃ₗ[ℂ] ↥Wm := LinearEquiv.ofLinear (B.restrict hBpm) ((-B).restrict hBmp)
      (LinearMap.ext fun x => Subtype.ext (by
        simpa [LinearMap.restrict_apply] using hcomp₁ (x : V)))
      (LinearMap.ext fun x => Subtype.ext (by
        simpa [LinearMap.restrict_apply] using hcomp₂ (x : V)))
    have hrank : finrank ℂ ↥Wp = finrank ℂ ↥Wm := e.finrank_eq
    have hdim : finrank ℂ V = 2 * finrank ℂ ↥Wp := by
      have hh := Submodule.finrank_sup_add_finrank_inf_eq Wp Wm
      rw [hsup, hinf, finrank_top, finrank_bot] at hh
      omega
    -- the residual `2k` structures on the halved space
    set idx : Fin (2 * k) → Fin (2 * (k + 1)) :=
      fun j => ⟨(j : ℕ) + 2, by have := j.isLt; omega⟩ with hidx
    have hidx0 : ∀ j, i₀ ≠ idx j := by
      intro j
      simp [hi₀, hidx, Fin.ext_iff]
    have hidx1 : ∀ j, i₁ ≠ idx j := by
      intro j
      simp [hi₁, hidx, Fin.ext_iff]
    have hidxne : ∀ j l : Fin (2 * k), j ≠ l → idx j ≠ idx l := by
      intro j l hjl h
      rw [hidx, Fin.mk.injEq] at h
      exact hjl (Fin.ext (by omega))
    have hAJx : ∀ (j : Fin (2 * k)) (x : V), A (J (idx j) x) = -(J (idx j) (A x)) :=
      fun j => end_anticomm_apply (hanti i₀ (idx j) (hidx0 j))
    have hJBx : ∀ (j : Fin (2 * k)) (x : V), J (idx j) (B x) = -(B (J (idx j) x)) :=
      fun j => end_anticomm_apply (hanti (idx j) i₁ (Ne.symm (hidx1 j)))
    have hpres : ∀ j : Fin (2 * k), ∀ x ∈ Wp, (B * J (idx j)) x ∈ Wp := by
      intro j x hx
      rw [hmemp] at hx
      rw [hmemp, Module.End.mul_apply, hABx, hAJx, hx, map_neg, map_smul, map_smul, neg_neg]
    set L : Fin (2 * k) → Module.End ℂ ↥Wp := fun j => (B * J (idx j)).restrict (hpres j)
      with hL
    have hCx : ∀ (j l : Fin (2 * k)) (x : V),
        B (J (idx j) (B (J (idx l) x))) = J (idx j) (J (idx l) x) := by
      intro j l x
      rw [hJBx j (J (idx l) x), map_neg, hB2x, neg_neg]
    have hLsq : ∀ j, L j * L j = -1 := by
      intro j
      refine LinearMap.ext fun x => Subtype.ext ?_
      have hx : B (J (idx j) (B (J (idx j) (x : V)))) = -(x : V) := by
        rw [hCx j j, end_sq_apply (hsq (idx j))]
      simpa [hL, LinearMap.restrict_apply, Module.End.mul_apply] using hx
    have hLanti : ∀ j l, j ≠ l → L j * L l = -(L l * L j) := by
      intro j l hjl
      refine LinearMap.ext fun x => Subtype.ext ?_
      have hx : B (J (idx j) (B (J (idx l) (x : V)))) =
          -(B (J (idx l) (B (J (idx j) (x : V))))) := by
        rw [hCx j l, hCx l j]
        exact end_anticomm_apply (hanti (idx j) (idx l) (hidxne j l hjl)) (x : V)
      simpa [hL, LinearMap.restrict_apply, Module.End.mul_apply] using hx
    obtain ⟨c, hc⟩ := ih ↥Wp L hLsq hLanti
    exact ⟨c, by rw [hdim, hc, pow_succ]; ring⟩

/-- **Clifford dimension divisibility**, packaged: `2k` anticommuting complex structures force
`2^k ∣ dim`. -/
theorem pow_dvd_finrank_of_anticomm [FiniteDimensional ℂ V] {k : ℕ}
    (J : Fin (2 * k) → Module.End ℂ V) (hsq : ∀ i, J i * J i = -1)
    (hanti : ∀ i j, i ≠ j → J i * J j = -(J j * J i)) : 2 ^ k ∣ finrank ℂ V :=
  pow_dvd_finrank_aux k V J hsq hanti

/-- **The Clifford multiplicity mechanism.**  If `2k` anticommuting complex structures commute
with `K`, they preserve every generalized eigenspace of `K`, so every algebraic multiplicity of
`K` is divisible by `2^k` — at every eigenvalue, real or not, with no location constraint. -/
theorem pow_dvd_finrank_maxGenEigenspace_of_anticomm [FiniteDimensional ℂ V] {k : ℕ}
    (K : Module.End ℂ V) (J : Fin (2 * k) → Module.End ℂ V)
    (hsq : ∀ i, J i * J i = -1) (hanti : ∀ i j, i ≠ j → J i * J j = -(J j * J i))
    (hcomm : ∀ i, Commute (J i) K) (lam : ℂ) :
    2 ^ k ∣ finrank ℂ (K.maxGenEigenspace lam) := by
  have hpres : ∀ i, ∀ x ∈ K.maxGenEigenspace lam, (J i) x ∈ K.maxGenEigenspace lam := by
    intro i x hx
    rw [Module.End.mem_maxGenEigenspace] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have hc : Commute (J i) ((K - lam • 1) ^ n) :=
      (((hcomm i).sub_right ((Commute.one_right (J i)).smul_right lam))).pow_right n
    calc ((K - lam • 1) ^ n) (J i x)
        = ((K - lam • 1) ^ n * J i) x := by rw [Module.End.mul_apply]
      _ = (J i * (K - lam • 1) ^ n) x := by rw [hc.eq]
      _ = J i (((K - lam • 1) ^ n) x) := by rw [Module.End.mul_apply]
      _ = 0 := by rw [hn, map_zero]
  refine pow_dvd_finrank_of_anticomm (fun i => (J i).restrict (hpres i)) ?_ ?_
  · intro i
    refine LinearMap.ext fun x => Subtype.ext ?_
    simpa [LinearMap.restrict_apply, Module.End.mul_apply] using
      end_sq_apply (hsq i) (x : V)
  · intro i j hij
    refine LinearMap.ext fun x => Subtype.ext ?_
    simpa [LinearMap.restrict_apply, Module.End.mul_apply] using
      end_anticomm_apply (hanti i j hij) (x : V)

end Mechanism

/-! ## Clifford window models and the rung bridge -/

/-- A Clifford window model at level `k` and point `ρ`: an endomorphism of a
finite-dimensional space, commuting with `2k` anticommuting complex structures, whose
algebraic multiplicity at `ρ` is ξ's vanishing order there. -/
structure CliffordModel (k : ℕ) (ρ : ℂ) : Type 1 where
  V : Type
  [addCommGroup_V : AddCommGroup V]
  [module_V : Module ℂ V]
  [finiteDimensional_V : FiniteDimensional ℂ V]
  K : Module.End ℂ V
  J : Fin (2 * k) → Module.End ℂ V
  square : ∀ i, J i * J i = -1
  anticomm : ∀ i j, i ≠ j → J i * J j = -(J j * J i)
  commutes : ∀ i, Commute (J i) K
  mult : finrank ℂ (K.maxGenEigenspace ρ) = (analyticOrderAt xi ρ).toNat

attribute [instance] CliffordModel.addCommGroup_V CliffordModel.module_V
  CliffordModel.finiteDimensional_V

/-- **The Clifford mechanism yields the rung**: models at every off-line zero force
`2^k`-divisibility of every off-line order. -/
theorem rhLadder_of_cliffordModel {k : ℕ}
    (h : ∀ ρ ∈ rightHalf, xi ρ = 0 → Nonempty (CliffordModel k ρ)) : RHLadder k := by
  rw [rhLadder_iff_toNat_dvd]
  intro ρ hρ hzero
  obtain ⟨M⟩ := h ρ hρ hzero
  rw [← M.mult]
  exact pow_dvd_finrank_maxGenEigenspace_of_anticomm M.K M.J M.square M.anticomm M.commutes ρ

/-! ## Existence of anticommuting families: the doubling construction -/

/-- A finite-dimensional space of dimension `2^k · m` carrying `2k` anticommuting complex
structures — a `Cl_{2k}(ℂ)`-module of the minimal dimension pattern. -/
structure AnticommSpace (k m : ℕ) : Type 1 where
  V : Type
  [addCommGroup_V : AddCommGroup V]
  [module_V : Module ℂ V]
  [finiteDimensional_V : FiniteDimensional ℂ V]
  J : Fin (2 * k) → Module.End ℂ V
  square : ∀ i, J i * J i = -1
  anticomm : ∀ i j, i ≠ j → J i * J j = -(J j * J i)
  dim : finrank ℂ V = 2 ^ k * m

attribute [instance] AnticommSpace.addCommGroup_V AnticommSpace.module_V
  AnticommSpace.finiteDimensional_V

/-- Level `0`: the bare space with the empty family. -/
noncomputable def AnticommSpace.base (m : ℕ) : AnticommSpace 0 m where
  V := Fin m → ℂ
  J := fun i => i.elim0
  square := fun i => i.elim0
  anticomm := fun i => i.elim0
  dim := by simp

section Doubling

variable {W : Type} [AddCommGroup W] [Module ℂ W]

/-- The lift of a structure to the doubled space, with a sign twist on the second factor. -/
private def liftJ (f : Module.End ℂ W) : Module.End ℂ (W × W) := f.prodMap (-f)

/-- The first new generator on the doubled space: `(x, y) ↦ (i·y, i·x)`. -/
private def genA : Module.End ℂ (W × W) :=
  (Complex.I • LinearMap.snd ℂ W W).prod (Complex.I • LinearMap.fst ℂ W W)

/-- The second new generator on the doubled space: `(x, y) ↦ (y, -x)`. -/
private def genB : Module.End ℂ (W × W) :=
  (LinearMap.snd ℂ W W).prod (-(LinearMap.fst ℂ W W))

private theorem liftJ_apply (f : Module.End ℂ W) (p : W × W) :
    liftJ f p = (f p.1, -(f p.2)) := rfl

private theorem genA_apply (p : W × W) :
    (genA : Module.End ℂ (W × W)) p = (Complex.I • p.2, Complex.I • p.1) := rfl

private theorem genB_apply (p : W × W) :
    (genB : Module.End ℂ (W × W)) p = (p.2, -p.1) := rfl

private theorem liftJ_sq {f : Module.End ℂ W} (hf : f * f = -1) : liftJ f * liftJ f = -1 := by
  refine LinearMap.ext fun p => ?_
  have h1 := end_sq_apply hf p.1
  have h2 := end_sq_apply hf p.2
  simp [Module.End.mul_apply, liftJ_apply, Prod.ext_iff, h1, h2]

private theorem liftJ_anticomm {f g : Module.End ℂ W} (h : f * g = -(g * f)) :
    liftJ f * liftJ g = -(liftJ g * liftJ f) := by
  refine LinearMap.ext fun p => ?_
  have h1 := end_anticomm_apply h p.1
  have h2 := end_anticomm_apply h p.2
  simp [Module.End.mul_apply, liftJ_apply, h1, h2]

private theorem genA_sq : (genA : Module.End ℂ (W × W)) * genA = -1 := by
  refine LinearMap.ext fun p => ?_
  simp [Module.End.mul_apply, genA_apply, Prod.ext_iff, smul_smul, Complex.I_mul_I]

private theorem genB_sq : (genB : Module.End ℂ (W × W)) * genB = -1 := by
  refine LinearMap.ext fun p => ?_
  simp [Module.End.mul_apply, genB_apply, Prod.ext_iff]

private theorem genA_genB :
    (genA : Module.End ℂ (W × W)) * genB = -(genB * genA) := by
  refine LinearMap.ext fun p => ?_
  simp [Module.End.mul_apply, genA_apply, genB_apply]

private theorem liftJ_genA (f : Module.End ℂ W) :
    liftJ f * genA = -(genA * liftJ f) := by
  refine LinearMap.ext fun p => ?_
  simp [Module.End.mul_apply, liftJ_apply, genA_apply, map_smul]

private theorem liftJ_genB (f : Module.End ℂ W) :
    liftJ f * genB = -(genB * liftJ f) := by
  refine LinearMap.ext fun p => ?_
  simp [Module.End.mul_apply, liftJ_apply, genB_apply]

end Doubling

private theorem anticomm_symm {R : Type*} [Ring R] {a b : R} (h : a * b = -(b * a)) :
    b * a = -(a * b) := by
  rw [h, neg_neg]

/-- Doubling: a level-`k` family on `V` yields a level-`k+1` family on `V × V`, doubling the
dimension — the module-level face of `Cl_{n+2} ≅ Cl_n ⊗ M₂`. -/
def AnticommSpace.double {k m : ℕ} (S : AnticommSpace k m) : AnticommSpace (k + 1) m where
  V := S.V × S.V
  J := Fin.snoc (Fin.snoc (fun j => liftJ (S.J j)) genA) genB
  square := by
    refine Fin.lastCases ?_ (fun i => ?_)
    · simp only [Fin.snoc_last]
      exact genB_sq
    · simp only [Fin.snoc_castSucc]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        exact genA_sq
      · simp only [Fin.snoc_castSucc]
        exact liftJ_sq (S.square j)
  anticomm := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact fun h => absurd rfl h
      | cast j' =>
        intro _
        induction j' using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact anticomm_symm genA_genB
        | cast j'' =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact anticomm_symm (liftJ_genB (S.J j''))
    | cast i' =>
      induction i' using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          intro _
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact genA_genB
        | cast j' =>
          induction j' using Fin.lastCases with
          | last => exact fun h => absurd rfl h
          | cast j'' =>
            intro _
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            exact anticomm_symm (liftJ_genA (S.J j''))
      | cast i'' =>
        induction j using Fin.lastCases with
        | last =>
          intro _
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact liftJ_genB (S.J i'')
        | cast j' =>
          induction j' using Fin.lastCases with
          | last =>
            intro _
            simp only [Fin.snoc_last, Fin.snoc_castSucc]
            exact liftJ_genA (S.J i'')
          | cast j'' =>
            intro hne
            simp only [Fin.snoc_castSucc]
            refine liftJ_anticomm (S.anticomm i'' j'' fun h => hne ?_)
            rw [h]
  dim := by
    rw [Module.finrank_prod, S.dim, pow_succ]
    ring

/-- Anticommuting families of every size exist over every base dimension. -/
theorem AnticommSpace.nonempty (k m : ℕ) : Nonempty (AnticommSpace k m) := by
  induction k with
  | zero => exact ⟨base m⟩
  | succ k ih =>
    obtain ⟨S⟩ := ih
    exact ⟨S.double⟩

/-- **Divisible orders admit Clifford models**: the scalar endomorphism of a `Cl_{2k}`-module
of dimension exactly the order realizes the multiplicity, and scalars commute with
everything. -/
theorem cliffordModel_of_pow_dvd_order {k : ℕ} {ρ : ℂ}
    (h : 2 ^ k ∣ (analyticOrderAt xi ρ).toNat) : Nonempty (CliffordModel k ρ) := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨S⟩ := AnticommSpace.nonempty k m
  have htop : ((ρ • 1 : Module.End ℂ S.V)).maxGenEigenspace ρ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simp⟩
  refine ⟨{ V := S.V, K := ρ • 1, J := S.J, square := S.square, anticomm := S.anticomm,
            commutes := fun i => (Commute.one_right (S.J i)).smul_right ρ, mult := ?_ }⟩
  rw [htop, finrank_top, S.dim]
  exact hm.symm

/-- **The Clifford reading of every rung.**  `RHLadder k` holds iff every right-half ξ-zero
order is the algebraic multiplicity, at that zero, of an endomorphism commuting with `2k`
anticommuting complex structures.  Divisibility of a vanishing order by `2^k` is exactly the
existence of a `Cl_{2k}(ℂ)`-symmetry on a finite-dimensional model of the local divisor. -/
theorem rhLadder_iff_cliffordModel (k : ℕ) :
    RHLadder k ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → Nonempty (CliffordModel k ρ) := by
  constructor
  · intro hlad ρ hρ hzero
    exact cliffordModel_of_pow_dvd_order ((rhLadder_iff_toNat_dvd k).mp hlad ρ hρ hzero)
  · exact rhLadder_of_cliffordModel

/-! ## Tower coherence and the capstones -/

/-- **Tower coherence**: forgetting generators restricts a level-`k` model to every lower
level — the model-level face of the ladder's downward nesting. -/
def CliffordModel.restrictLevel {k m : ℕ} (hmk : m ≤ k) {ρ : ℂ} (M : CliffordModel k ρ) :
    CliffordModel m ρ where
  V := M.V
  K := M.K
  J := fun i => M.J (Fin.castLE (by omega) i)
  square := fun i => M.square _
  anticomm := fun i j hij => M.anticomm _ _ (fun h => hij (Fin.castLE_injective _ h))
  commutes := fun i => M.commutes _
  mult := M.mult

/-- Model existence is antitone in the level. -/
theorem cliffordModel_mono {k m : ℕ} (hmk : m ≤ k) {ρ : ℂ}
    (h : Nonempty (CliffordModel k ρ)) : Nonempty (CliffordModel m ρ) := by
  obtain ⟨M⟩ := h
  exact ⟨M.restrictLevel hmk⟩

/-- The successor case of coherence: a level-`k+1` model restricts to level `k`, matching the
Kummer squaring law's downward nesting `rhLadder_of_succ`. -/
theorem cliffordModel_of_succ {k : ℕ} {ρ : ℂ}
    (h : Nonempty (CliffordModel (k + 1) ρ)) : Nonempty (CliffordModel k ρ) :=
  cliffordModel_mono (Nat.le_succ k) h

/-- **RH ⟺ Clifford models at every level at every off-line zero.** -/
theorem rh_iff_forall_cliffordModel :
    RiemannHypothesis ↔ ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 → Nonempty (CliffordModel k ρ) := by
  rw [rh_iff_forall_ladder]
  exact forall_congr' fun k => rhLadder_iff_cliffordModel k

/-- **RH from cofinally many Clifford levels**: models at unboundedly many levels suffice. -/
theorem rh_of_cliffordModel_cofinal
    (h : ∀ N, ∃ k, N ≤ k ∧ ∀ ρ ∈ rightHalf, xi ρ = 0 → Nonempty (CliffordModel k ρ)) :
    RiemannHypothesis := by
  refine rh_of_rhLadder_cofinal fun N => ?_
  obtain ⟨k, hk, hmod⟩ := h N
  exact ⟨k, hk, rhLadder_of_cliffordModel hmod⟩

end RHTower
