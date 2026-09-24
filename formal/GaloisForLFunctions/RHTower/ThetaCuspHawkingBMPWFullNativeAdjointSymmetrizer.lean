import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCovector
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceDifferential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspIndicialSelection

/-!
# PW-B full/native adjoint-current obstruction

The literal full kernel has angular forcing `λ (K_full + K_native)`; the native
kernel carries its angular Laplacian.  Their fixed-angular-mode operator is
triangular.  A symmetric two-channel current with coefficients independent of
angular mode is necessarily blind to the full channel.  The first nondegenerate
local symmetrizer instead contains one angular Laplacian, and the actual
source vertex lands entirely in its native dual channel.  This is a scoped
obstruction to a constant same-response current, not a no-go for adjoint or
noncompact boundary currents.
-/

namespace RHTower.D4BMPWFullNativeAdjointSymmetrizer

open GaloisForLFunctions.HTGeometry
open D4BMModularCore D4BMHorizon D4BMGlobalAngularResponse

noncomputable section
set_option autoImplicit false

/-- Angular-mode action induced by the literal full/native kernel equations. -/
def modeAction (lam mu : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (lam * (p.1 + p.2), mu * p.2)

/-- Algebraic transpose of the triangular mode action. -/
def modeAdjointAction (lam mu : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (lam * p.1, lam * p.1 + mu * p.2)

/-- General mode-independent symmetric two-channel bilinear coefficient. -/
def constantSymmetrizer (a b c : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (a * p.1 + b * p.2, b * p.1 + c * p.2)

def CompatibleAtEveryMode (lam a b c : ℂ) : Prop :=
  ∀ (mu : ℂ) (p : ℂ × ℂ),
    constantSymmetrizer a b c (modeAction lam mu p) =
      modeAdjointAction lam mu (constantSymmetrizer a b c p)

def CompatibleAtTwoModes (lam a b c : ℂ) : Prop :=
  ∀ p : ℂ × ℂ,
    constantSymmetrizer a b c (modeAction lam 0 p) =
        modeAdjointAction lam 0 (constantSymmetrizer a b c p) ∧
      constantSymmetrizer a b c (modeAction lam lam p) =
        modeAdjointAction lam lam (constantSymmetrizer a b c p)

private theorem compatible_only_native (lam a b c : ℂ) (hlam : lam ≠ 0)
    (h : CompatibleAtTwoModes lam a b c) : a = 0 ∧ b = 0 := by
  have h0 := congrArg Prod.fst ((h (0, 1)).1)
  have h1 := congrArg Prod.fst ((h (0, 1)).2)
  dsimp [constantSymmetrizer, modeAction, modeAdjointAction] at h0 h1
  have ha0 : lam * a = 0 := by linear_combination h1
  have ha : a = 0 := (mul_eq_zero.mp ha0).resolve_left hlam
  have hb : b = 0 := by
    rw [ha] at h0
    have hb0 : lam * b = 0 := by linear_combination -h0
    exact (mul_eq_zero.mp hb0).resolve_left hlam
  exact ⟨ha, hb⟩

/-- Two actual angular rates, zero and the source-scalar rate, already force
every mode-independent symmetric current to lose its full-channel readout. -/
theorem no_constant_two_mode_full_channel_symmetrizer (lam : ℂ) (hlam : lam ≠ 0) :
    ¬ ∃ a b c : ℂ, CompatibleAtTwoModes lam a b c ∧ (a ≠ 0 ∨ b ≠ 0) := by
  rintro ⟨a, b, c, h, hab⟩
  obtain ⟨ha, hb⟩ := compatible_only_native lam a b c hlam h
  exact hab.elim (fun hne => hne ha) (fun hne => hne hb)

theorem no_constant_full_channel_symmetrizer (lam : ℂ) (hlam : lam ≠ 0) :
    ¬ ∃ a b c : ℂ, CompatibleAtEveryMode lam a b c ∧ (a ≠ 0 ∨ b ≠ 0) := by
  rintro ⟨a, b, c, h, hab⟩
  exact no_constant_two_mode_full_channel_symmetrizer lam hlam
    ⟨a, b, c, (fun p => ⟨h 0 p, h lam p⟩), hab⟩

private theorem physical_parameter_ne_zero (q : XiZeroCopy) (branch : Bool) :
    parameter q branch ≠ 0 := by
  have hr := (D4BMCuspProjection.physicalRate_re_bounds q branch).2
  have hne (c : ℝ) (hc : c ≤ 2) :
      D4BMCuspProjection.physicalRate q branch + (c : ℂ) ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hreal
    linarith
  rw [D4BMCuspProjection.physicalRate_parameter]
  exact mul_ne_zero (hne 1 (by norm_num)) (hne 2 (by norm_num))

/-- For the actual Xi-labelled coupling, no angular-mode-independent
symmetric current can read the full response channel at every mode. -/
theorem physical_no_constant_full_channel_symmetrizer (q : XiZeroCopy)
    (branch : Bool) :
    ¬ ∃ a b c : ℂ, CompatibleAtTwoModes (parameter q branch) a b c ∧
      (a ≠ 0 ∨ b ≠ 0) :=
  no_constant_two_mode_full_channel_symmetrizer _ (physical_parameter_ne_zero q branch)

/-- Minimal first-order angular-mode symmetrizer. Its off-diagonal channel
retains the full/native coupling instead of suppressing it. -/
def derivativeSymmetrizer (lam mu : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  ((mu - lam) * p.1 - lam * p.2, -lam * p.1)

theorem derivativeSymmetrizer_intertwines (lam mu : ℂ) (p : ℂ × ℂ) :
    derivativeSymmetrizer lam mu (modeAction lam mu p) =
      modeAdjointAction lam mu (derivativeSymmetrizer lam mu p) := by
  rcases p with ⟨u, n⟩
  apply Prod.ext
  · dsimp [derivativeSymmetrizer, modeAction, modeAdjointAction]
    ring
  · dsimp [derivativeSymmetrizer, modeAction, modeAdjointAction]
    ring

theorem derivativeSymmetrizer_injective (lam mu : ℂ) (hlam : lam ≠ 0) :
    Function.Injective (derivativeSymmetrizer lam mu) := by
  rintro ⟨u, n⟩ ⟨v, m⟩ h
  have hfirst := congrArg Prod.fst h
  have hsecond := congrArg Prod.snd h
  dsimp [derivativeSymmetrizer] at hfirst hsecond
  have hu : u = v := by
    have hz : lam * (u - v) = 0 := by linear_combination -hsecond
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hlam)
  have hn : n = m := by
    rw [hu] at hfirst
    have hz : lam * (n - m) = 0 := by linear_combination -hfirst
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hlam)
  simp [hu, hn]

/-- At any angular mode satisfying the actual full-field vertex equation,
the local symmetrizer annihilates the full dual source component. -/
theorem derivativeSymmetrizer_source_native_only (lam mu H Q : ℂ)
    (hsource : mu * H = lam * (H + Q)) :
    derivativeSymmetrizer lam mu (H, Q) = (0, -lam * H) := by
  apply Prod.ext
  · dsimp [derivativeSymmetrizer]
    linear_combination hsource
  · rfl

/-- The first dual component vanishes for the *actual* theta full/square
vertex, with its original scalar Laplacian and no angular-mode substitution. -/
theorem physical_source_full_dual_zero (q : XiZeroCopy) (branch : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    scalarLaplacian (fullAngularField q branch) z -
      parameter q branch *
        (fullAngularField q branch z + fullSquarePotential q z) = 0 := by
  rw [fullAngularField_equation q branch z hz]
  unfold fullSquarePotential
  ring

theorem physical_source_derivative_symmetrizer (q : XiZeroCopy) (branch : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (scalarLaplacian (fullAngularField q branch) z -
        parameter q branch *
          (fullAngularField q branch z + fullSquarePotential q z),
      -parameter q branch * fullAngularField q branch z) =
      (0, -parameter q branch * fullAngularField q branch z) := by
  apply Prod.ext
  · exact physical_source_full_dual_zero q branch z hz
  · rfl

/-- Source contact through the local full/native symmetrizer is exactly an
angular Green commutator plus a native-channel contact. The literal full
response cannot be isolated by silently dropping either term. -/
theorem physical_source_adjoint_contact_decomposition (q : XiZeroCopy)
    (branch : Bool) (U N : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) :
    fullAngularField q branch z *
        (scalarLaplacian U z - parameter q branch * (U z + N z)) -
      parameter q branch * fullSquarePotential q z * U z =
    fullAngularField q branch z * scalarLaplacian U z -
      U z * scalarLaplacian (fullAngularField q branch) z -
        parameter q branch * fullAngularField q branch z * N z := by
  linear_combination (U z) * (physical_source_full_dual_zero q branch z hz)

end
end RHTower.D4BMPWFullNativeAdjointSymmetrizer
