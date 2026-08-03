import GaloisForLFunctions.HTGeometry.FullExponentialJetGauge
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The spectral inversion gauge: precomposition with `w ↦ 1/w`

Precomposing a family with the inversion of the spectral variable is a change of variable, not a
polynomial operation on jets.  Its jets are triangular with universal coefficients: differentiating
in `w` corresponds, in the coordinate `z = 1/w`, to the derivation `-z² d/dz`, which preserves the
jet polynomial ring.  So the composed jets are polynomials in the jets of the family, and only the
spectral variable itself needs inverting.

The substitution therefore lands in the jet ring with the spectral variable inverted, and it is
injective because every jet point with nonzero spectral coordinate is the jet point of a composed
family — realize the prescription directly and precompose it back.  Clearing the spectral
denominators then carries a differential relation for the composed family to one for the family.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Universal numerators of the jets of a family precomposed with the spectral inversion: applying
`-z² d/dz` repeatedly to the zeroth jet. -/
def compInvNumer (m : ℕ) (i : Fin m) : ℕ → MvPolynomial (FullJetIndex m) ℂ
  | 0 => MvPolynomial.X (Sum.inr (i, 0))
  | (k + 1) => -(MvPolynomial.X (Sum.inl ())) ^ 2 * fullJetDerivation m (compInvNumer m i k)

@[simp] theorem compInvNumer_zero (m : ℕ) (i : Fin m) :
    compInvNumer m i 0 = MvPolynomial.X (Sum.inr (i, 0)) := rfl

theorem compInvNumer_succ (m : ℕ) (i : Fin m) (k : ℕ) :
    compInvNumer m i (k + 1)
      = -(MvPolynomial.X (Sum.inl ())) ^ 2 * fullJetDerivation m (compInvNumer m i k) := rfl

section ChainRule

variable {m : ℕ} {U V : Set ℂ} {g : Fin m → ℂ → ℂ}

/-- **The chain rule through the spectral inversion.**  Differentiating in `w` the evaluation of a
jet polynomial at the jets taken at `1/w` is evaluating the derivation `-z² d/dz`. -/
theorem deriv_eval_fullJetVec_inv (hUo : IsOpen U)
    (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) {w : ℂ} (hw : w ≠ 0) (hwU : w⁻¹ ∈ U)
    (P : MvPolynomial (FullJetIndex m) ℂ) :
    deriv (fun v => MvPolynomial.eval (fullJetVec g v⁻¹) P) w
      = MvPolynomial.eval (fullJetVec g w⁻¹)
        (-(MvPolynomial.X (Sum.inl ())) ^ 2 * fullJetDerivation m P) := by
  have hF : DifferentiableAt ℂ (fun z => MvPolynomial.eval (fullJetVec g z) P) w⁻¹ :=
    differentiableAt_eval_fullJetVec hUo hg hwU P
  have hinv : DifferentiableAt ℂ (fun v : ℂ => v⁻¹) w := differentiableAt_inv hw
  have hcomp : (fun v : ℂ => MvPolynomial.eval (fullJetVec g v⁻¹) P)
      = (fun z => MvPolynomial.eval (fullJetVec g z) P) ∘ (fun v : ℂ => v⁻¹) := rfl
  rw [hcomp, deriv_comp w hF hinv, deriv_eval_fullJetVec hUo hg hwU P, deriv_inv]
  simp only [map_mul, map_neg, map_pow, MvPolynomial.eval_X, fullJetVec_inl]
  rw [inv_pow]
  ring

/-- **The composed jets.**  Every jet of `g i (1/w)` is the universal numerator evaluated at the
jets of `g` at `1/w`. -/
theorem iteratedDeriv_comp_inv_eq (hUo : IsOpen U)
    (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) (hVo : IsOpen V)
    (hV0 : ∀ v ∈ V, v ≠ 0) (hVU : ∀ v ∈ V, v⁻¹ ∈ U) (i : Fin m) (k : ℕ) :
    ∀ w ∈ V, iteratedDeriv k (fun v => g i v⁻¹) w
      = MvPolynomial.eval (fullJetVec g w⁻¹) (compInvNumer m i k) := by
  induction k with
  | zero =>
      intro w _
      rw [iteratedDeriv_zero, compInvNumer_zero, MvPolynomial.eval_X, fullJetVec_inr,
        iteratedDeriv_zero]
  | succ k ih =>
      intro w hw
      have hEq : (fun v => iteratedDeriv k (fun u => g i u⁻¹) v)
          =ᶠ[nhds w] fun v => MvPolynomial.eval (fullJetVec g v⁻¹) (compInvNumer m i k) := by
        filter_upwards [hVo.mem_nhds hw] with v hv
        exact ih v hv
      rw [iteratedDeriv_succ, hEq.deriv_eq,
        deriv_eval_fullJetVec_inv hUo hg (hV0 w hw) (hVU w hw) (compInvNumer m i k),
        compInvNumer_succ]

end ChainRule

/-- The jet ring with the spectral variable inverted. -/
abbrev SpectralAway (m : ℕ) :=
  Localization.Away (MvPolynomial.X (Sum.inl ()) : MvPolynomial (FullJetIndex m) ℂ)

/-- The inverse of the spectral variable in the localization. -/
def invSpectral (m : ℕ) : SpectralAway m :=
  IsLocalization.Away.invSelf (MvPolynomial.X (Sum.inl ()) : MvPolynomial (FullJetIndex m) ℂ)

theorem algebraMap_spectral_mul_invSpectral (m : ℕ) :
    algebraMap (MvPolynomial (FullJetIndex m) ℂ) (SpectralAway m)
        (MvPolynomial.X (Sum.inl ())) * invSpectral m = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- The substitution attached to precomposing a family with the spectral inversion. -/
def compInvSubst (m : ℕ) : FullJetIndex m → SpectralAway m :=
  Sum.elim (fun _ => invSpectral m)
    (fun p => algebraMap (MvPolynomial (FullJetIndex m) ℂ) (SpectralAway m)
      (compInvNumer m p.1 p.2))

/-- The substitution as an algebra homomorphism into the localization. -/
def compInvAlgHom (m : ℕ) : MvPolynomial (FullJetIndex m) ℂ →ₐ[ℂ] SpectralAway m :=
  MvPolynomial.aeval (compInvSubst m)

section Eval

variable {m : ℕ} {x : FullJetIndex m → ℂ}

theorem isUnit_eval_spectral_pow (hx : x (Sum.inl ()) ≠ 0)
    (y : Submonoid.powers (MvPolynomial.X (Sum.inl ()) : MvPolynomial (FullJetIndex m) ℂ)) :
    IsUnit (MvPolynomial.aeval x (y : MvPolynomial (FullJetIndex m) ℂ)) := by
  obtain ⟨k, hk⟩ := y.2
  have hval : MvPolynomial.aeval x (y : MvPolynomial (FullJetIndex m) ℂ)
      = (MvPolynomial.aeval x (MvPolynomial.X (Sum.inl ()) :
          MvPolynomial (FullJetIndex m) ℂ)) ^ k := by
    rw [← hk, map_pow]
  rw [hval]
  refine IsUnit.pow k ?_
  rw [isUnit_iff_ne_zero, MvPolynomial.aeval_X]
  exact hx

/-- Evaluation at a jet point with nonzero spectral coordinate, extended to the localization. -/
def evalSpectralAway (hx : x (Sum.inl ()) ≠ 0) : SpectralAway m →ₐ[ℂ] ℂ :=
  IsLocalization.liftAlgHom (isUnit_eval_spectral_pow hx)

@[simp]
theorem evalSpectralAway_algebraMap (hx : x (Sum.inl ()) ≠ 0)
    (p : MvPolynomial (FullJetIndex m) ℂ) :
    evalSpectralAway hx (algebraMap _ _ p) = MvPolynomial.aeval x p := by
  rw [evalSpectralAway, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem evalSpectralAway_invSpectral (hx : x (Sum.inl ()) ≠ 0) :
    evalSpectralAway hx (invSpectral m) = (x (Sum.inl ()))⁻¹ := by
  have hmul := congrArg (evalSpectralAway hx) (algebraMap_spectral_mul_invSpectral m)
  rw [map_mul, map_one, evalSpectralAway_algebraMap, MvPolynomial.aeval_X] at hmul
  calc evalSpectralAway hx (invSpectral m)
      = (x (Sum.inl ()))⁻¹ * (x (Sum.inl ()) * evalSpectralAway hx (invSpectral m)) := by
        field_simp
    _ = (x (Sum.inl ()))⁻¹ := by rw [hmul, mul_one]

end Eval

/-- The jet point of the composed family attached to a jet point of the family. -/
def compInvJetPoint {m : ℕ} (x : FullJetIndex m → ℂ) : FullJetIndex m → ℂ :=
  Sum.elim (fun _ => (x (Sum.inl ()))⁻¹)
    (fun p => MvPolynomial.eval x (compInvNumer m p.1 p.2))

/-- Evaluating the substitution is evaluating at the composed jet point. -/
theorem evalSpectralAway_comp_compInvAlgHom {m : ℕ} {x : FullJetIndex m → ℂ}
    (hx : x (Sum.inl ()) ≠ 0) :
    (evalSpectralAway hx).comp (compInvAlgHom m) = MvPolynomial.aeval (compInvJetPoint x) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with u | ⟨i, k⟩
  · rw [AlgHom.comp_apply, compInvAlgHom, MvPolynomial.aeval_X, compInvSubst, Sum.elim_inl,
      evalSpectralAway_invSpectral, MvPolynomial.aeval_X]
    rfl
  · rw [AlgHom.comp_apply, compInvAlgHom, MvPolynomial.aeval_X, compInvSubst, Sum.elim_inr,
      evalSpectralAway_algebraMap, MvPolynomial.aeval_X]
    rfl

/-- For an actual family the composed jet point is the jet vector of the composed family. -/
theorem compInvJetPoint_fullJetVec {m : ℕ} {U V : Set ℂ} {g : Fin m → ℂ → ℂ} (hUo : IsOpen U)
    (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) (hVo : IsOpen V)
    (hV0 : ∀ v ∈ V, v ≠ 0) (hVU : ∀ v ∈ V, v⁻¹ ∈ U) {w : ℂ} (hw : w ∈ V) :
    compInvJetPoint (fullJetVec g w⁻¹) = fullJetVec (fun i v => g i v⁻¹) w := by
  funext v
  rcases v with u | ⟨i, k⟩
  · rw [compInvJetPoint, Sum.elim_inl, fullJetVec_inl, fullJetVec_inl, inv_inv]
  · rw [compInvJetPoint, Sum.elim_inr, fullJetVec_inr]
    exact (iteratedDeriv_comp_inv_eq hUo hg hVo hV0 hVU i k w hw).symm

/-- **The spectral inversion substitution is injective.**  Every jet point with nonzero spectral
coordinate is the jet point of a composed family, obtained by realizing the prescription and
precomposing it back. -/
theorem compInvAlgHom_injective (m : ℕ) : Function.Injective (compInvAlgHom m) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro P hP
  refine mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates
    {(Sum.inl () : FullJetIndex m)} P ?_
  intro y hy
  have hw₀ : y (Sum.inl ()) ≠ 0 := hy _ (Finset.mem_singleton_self _)
  set w₀ : ℂ := y (Sum.inl ()) with hw₀def
  set n : ℕ := fullJetOrder P with hn
  choose h hsmooth hcont hjet using
    fun i : Fin m => exists_smooth_iteratedDeriv_eq n w₀ (fun k => y (Sum.inr (i, k)))
  set U : Set ℂ := {z : ℂ | z ≠ 0} with hU
  have hUo : IsOpen U := isOpen_compl_singleton
  set g : Fin m → ℂ → ℂ := fun i z => h i z⁻¹ with hg
  have hgsmooth : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z := by
    intro i z hz
    exact (hsmooth i z⁻¹).comp z (contDiffAt_inv ℂ hz)
  have hV0 : ∀ v ∈ U, v ≠ 0 := fun v hv => hv
  have hVU : ∀ v ∈ U, v⁻¹ ∈ U := fun v hv => inv_ne_zero hv
  have hcompose : (fun i v => g i v⁻¹) = h := by
    funext i v
    show h i v⁻¹⁻¹ = h i v
    rw [inv_inv]
  have hx : fullJetVec g w₀⁻¹ (Sum.inl ()) ≠ 0 := by
    rw [fullJetVec_inl]
    exact inv_ne_zero hw₀
  have hagree := evalSpectralAway_comp_compInvAlgHom (x := fullJetVec g w₀⁻¹) hx
  have hzero : MvPolynomial.aeval (compInvJetPoint (fullJetVec g w₀⁻¹)) P = 0 := by
    have happ := congrArg (fun F : MvPolynomial (FullJetIndex m) ℂ →ₐ[ℂ] ℂ => F P) hagree
    simp only [AlgHom.comp_apply] at happ
    rw [← happ, hP, map_zero]
  have hpoint : compInvJetPoint (fullJetVec g w₀⁻¹) = fullJetVec h w₀ := by
    rw [compInvJetPoint_fullJetVec (g := g) hUo hgsmooth hUo hV0 hVU (w := w₀) hw₀, hcompose]
  rw [hpoint] at hzero
  have hvars : ∀ v ∈ P.vars, fullJetVec h w₀ v = y v := by
    intro v hv
    rcases v with u | ⟨i, k⟩
    · rw [fullJetVec_inl]
    · rw [fullJetVec_inr, hjet i k (le_fullJetOrder hv)]
  have hcongr : MvPolynomial.eval (fullJetVec h w₀) P = MvPolynomial.eval y P := by
    refine MvPolynomial.eval₂_congr _ _ _ ?_
    intro v d hvd hcoeff
    exact hvars v ((MvPolynomial.mem_vars_iff_mem_support v).mpr
      ⟨d, MvPolynomial.mem_support_iff.mpr hcoeff, hvd⟩)
  have hconv : MvPolynomial.aeval (fullJetVec h w₀) P
      = MvPolynomial.eval (fullJetVec h w₀) P := rfl
  rw [hconv, hcongr] at hzero
  exact hzero

/-- **The spectral inversion gauge.**  A differential relation for a family precomposed with the
spectral inversion produces a differential relation for the family itself, tested at the same
sample points. -/
theorem exists_fullJet_relation_of_comp_inv {m : ℕ} {U V W : Set ℂ} (hUo : IsOpen U)
    {g : Fin m → ℂ → ℂ} (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) (hVo : IsOpen V)
    (hV0 : ∀ v ∈ V, v ≠ 0) (hVU : ∀ v ∈ V, v⁻¹ ∈ U) {chi : ℂ → ℂ} (hchi : ∀ w ∈ W, chi w ∈ V)
    (P : MvPolynomial (FullJetIndex m) ℂ) (hPne : P ≠ 0)
    (hP : ∀ w ∈ W, MvPolynomial.eval (fullJetVec (fun i v => g i v⁻¹) (chi w)) P = 0) :
    ∃ Q : MvPolynomial (FullJetIndex m) ℂ, Q ≠ 0 ∧
      ∀ w ∈ W, MvPolynomial.eval (fullJetVec g (chi w)⁻¹) Q = 0 := by
  classical
  have hQne : compInvAlgHom m P ≠ 0 := by
    intro hcon
    exact hPne ((injective_iff_map_eq_zero (compInvAlgHom m)).mp (compInvAlgHom_injective m) P hcon)
  obtain ⟨⟨R, s⟩, hRs⟩ :=
    IsLocalization.mk'_surjective
      (Submonoid.powers (MvPolynomial.X (Sum.inl ()) : MvPolynomial (FullJetIndex m) ℂ))
      (compInvAlgHom m P)
  simp only at hRs
  have hRne : R ≠ 0 := by
    intro hcon
    rw [hcon, IsLocalization.mk'_zero] at hRs
    exact hQne hRs.symm
  refine ⟨R, hRne, ?_⟩
  intro w hw
  have hwV : chi w ∈ V := hchi w hw
  have hx : fullJetVec g (chi w)⁻¹ (Sum.inl ()) ≠ 0 := by
    rw [fullJetVec_inl]
    exact inv_ne_zero (hV0 _ hwV)
  have hagree := evalSpectralAway_comp_compInvAlgHom (x := fullJetVec g (chi w)⁻¹) hx
  have hPzero : evalSpectralAway hx (compInvAlgHom m P) = 0 := by
    have happ := congrArg (fun F : MvPolynomial (FullJetIndex m) ℂ →ₐ[ℂ] ℂ => F P) hagree
    simp only [AlgHom.comp_apply] at happ
    rw [happ, compInvJetPoint_fullJetVec hUo hg hVo hV0 hVU hwV]
    exact hP w hw
  have hspec : compInvAlgHom m P
      * algebraMap (MvPolynomial (FullJetIndex m) ℂ) (SpectralAway m)
          (s : MvPolynomial (FullJetIndex m) ℂ)
      = algebraMap (MvPolynomial (FullJetIndex m) ℂ) (SpectralAway m) R := by
    rw [← hRs]
    exact IsLocalization.mk'_spec _ _ _
  have hval := congrArg (evalSpectralAway hx) hspec
  rw [map_mul, hPzero, zero_mul, evalSpectralAway_algebraMap] at hval
  have hconv : MvPolynomial.aeval (fullJetVec g (chi w)⁻¹) R
      = MvPolynomial.eval (fullJetVec g (chi w)⁻¹) R := rfl
  rw [← hconv]
  exact hval.symm

/-- **Independence transports through the spectral inversion.**  If a family satisfies no
differential relation at the inverted sample points, neither does the precomposed family. -/
theorem fullJet_independent_comp_inv {m : ℕ} {U V W : Set ℂ} (hUo : IsOpen U)
    {g : Fin m → ℂ → ℂ} (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) (hVo : IsOpen V)
    (hV0 : ∀ v ∈ V, v ≠ 0) (hVU : ∀ v ∈ V, v⁻¹ ∈ U) {chi : ℂ → ℂ} (hchi : ∀ w ∈ W, chi w ∈ V)
    (hind : ∀ Q : MvPolynomial (FullJetIndex m) ℂ,
      (∀ w ∈ W, MvPolynomial.eval (fullJetVec g (chi w)⁻¹) Q = 0) → Q = 0)
    (P : MvPolynomial (FullJetIndex m) ℂ)
    (hP : ∀ w ∈ W, MvPolynomial.eval (fullJetVec (fun i v => g i v⁻¹) (chi w)) P = 0) : P = 0 := by
  by_contra hPne
  obtain ⟨Q, hQne, hQ⟩ :=
    exists_fullJet_relation_of_comp_inv hUo hg hVo hV0 hVU hchi P hPne hP
  exact hQne (hind Q hQ)

end

end GaloisForLFunctions.HTGeometry
