import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCovector
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSquareSourceDifferential
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspIndicialSelection

/-!
# PW-B full/native adjoint-current obstruction

The literal full kernel has angular forcing `λ (K_full + K_native)`; the native
kernel carries its angular Laplacian. Their fixed-angular-mode operator is
triangular. At nonzero coupling every algebraic modewise intertwiner with the
transpose is forced symmetric, and every physical source vertex lands in its
native dual channel. The full readout is exactly proportional to the
intertwining defect, which is skew for symmetric maps. This modewise result
does not eliminate global differential, adjoint, or noncompact boundary currents.
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

/-- Compatibility at one arbitrary angular mode; its coefficients may depend on that mode. -/
def CompatibleAtMode (lam mu a b c : ℂ) : Prop :=
  ∀ p : ℂ × ℂ,
    constantSymmetrizer a b c (modeAction lam mu p) =
      modeAdjointAction lam mu (constantSymmetrizer a b c p)

/-- Exact classification of all symmetric modewise intertwiners. The native-native
coefficient is free, but the full-channel coefficients obey one rigid relation. -/
theorem compatibleAtMode_iff (lam mu a b c : ℂ) :
    CompatibleAtMode lam mu a b c ↔ lam * a + (mu - lam) * b = 0 := by
  constructor
  · intro h
    have hc := congrArg Prod.fst (h (0, 1))
    dsimp [CompatibleAtMode, constantSymmetrizer, modeAction,
      modeAdjointAction] at hc
    linear_combination hc
  · intro h p
    rcases p with ⟨u, v⟩
    apply Prod.ext
    · dsimp [constantSymmetrizer, modeAction, modeAdjointAction]
      linear_combination v * h
    · dsimp [constantSymmetrizer, modeAction, modeAdjointAction]
      linear_combination -u * h

/-- Every compatible symmetric modewise current sends a source vertex of the
literal full/native triangular system to zero in the full dual channel. The
modewise coefficient choice and native-native coefficient are unrestricted. -/
theorem compatible_source_full_dual_zero (lam mu a b c H Q : ℂ)
    (hlam : lam ≠ 0) (hcompat : CompatibleAtMode lam mu a b c)
    (hsource : mu * H = lam * (H + Q)) :
    (constantSymmetrizer a b c (H, Q)).1 = 0 := by
  have hrel := (compatibleAtMode_iff lam mu a b c).mp hcompat
  have hsrc : (mu - lam) * H - lam * Q = 0 := by
    linear_combination hsource
  have hzero : lam * (a * H + b * Q) = 0 := by
    linear_combination H * hrel - b * hsrc
  exact (mul_eq_zero.mp hzero).resolve_left hlam

/-- No symmetric modewise intertwiner can retain a nonzero full dual contact at
a source vertex of the literal triangular action. -/
theorem no_modewise_full_contact (lam : ℂ) (hlam : lam ≠ 0) :
    ¬ ∃ mu H Q a b c : ℂ,
      CompatibleAtMode lam mu a b c ∧
      mu * H = lam * (H + Q) ∧
      (constantSymmetrizer a b c (H, Q)).1 ≠ 0 := by
  rintro ⟨mu, H, Q, a, b, c, hcompat, hsource, hne⟩
  exact hne (compatible_source_full_dual_zero lam mu a b c H Q hlam hcompat hsource)

/-- The actual Xi coupling is nonzero on both branches, so the full-channel
obstruction holds unconditionally for every physical Xi copy. -/
theorem physical_no_modewise_full_contact (q : XiZeroCopy) (branch : Bool) :
    ¬ ∃ mu H Q a b c : ℂ,
      CompatibleAtMode (parameter q branch) mu a b c ∧
      mu * H = parameter q branch * (H + Q) ∧
      (constantSymmetrizer a b c (H, Q)).1 ≠ 0 :=
  no_modewise_full_contact (parameter q branch) (physical_parameter_ne_zero q branch)

/-- An arbitrary modewise matrix, without a symmetry premise. -/
def arbitraryModeMap (a b c d : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (a * p.1 + b * p.2, c * p.1 + d * p.2)

def ArbitraryCompatibleAtMode (lam mu a b c d : ℂ) : Prop :=
  ∀ p : ℂ × ℂ,
    arbitraryModeMap a b c d (modeAction lam mu p) =
      modeAdjointAction lam mu (arbitraryModeMap a b c d p)

/-- Nonzero triangular coupling forces every modewise algebraic intertwiner to
be symmetric. The native-native coefficient remains free. -/
theorem arbitraryCompatible_iff (lam mu a b c d : ℂ) (hlam : lam ≠ 0) :
    ArbitraryCompatibleAtMode lam mu a b c d ↔
      b = c ∧ lam * a + (mu - lam) * b = 0 := by
  constructor
  · intro h
    have hf := congrArg Prod.fst (h (0, 1))
    have hs := congrArg Prod.snd (h (0, 1))
    dsimp [arbitraryModeMap, modeAction, modeAdjointAction] at hf hs
    have hbc : lam * (b - c) = 0 := by linear_combination -hs
    refine ⟨sub_eq_zero.mp ((mul_eq_zero.mp hbc).resolve_left hlam), ?_⟩
    linear_combination hf
  · rintro ⟨rfl, h⟩
    intro p
    change constantSymmetrizer a b d (modeAction lam mu p) =
      modeAdjointAction lam mu (constantSymmetrizer a b d p)
    exact (compatibleAtMode_iff lam mu a b d).mpr h p

/-- Every algebraic modewise dualization of a physical source vertex loses
its full dual component; symmetry was not an independent assumption. -/
theorem arbitraryCompatible_source_full_dual_zero
    (lam mu a b c d H Q : ℂ) (hlam : lam ≠ 0)
    (hcompat : ArbitraryCompatibleAtMode lam mu a b c d)
    (hsource : mu * H = lam * (H + Q)) :
    (arbitraryModeMap a b c d (H, Q)).1 = 0 := by
  obtain ⟨rfl, hrel⟩ := (arbitraryCompatible_iff lam mu a b c d hlam).mp hcompat
  change (constantSymmetrizer a b d (H, Q)).1 = 0
  exact compatible_source_full_dual_zero lam mu a b d H Q hlam
    ((compatibleAtMode_iff lam mu a b d).mpr hrel) hsource

/-- No arbitrary compatible modewise matrix restores a nonzero full dual
source contact for either Xi-labelled physical branch. -/
theorem physical_no_arbitrary_modewise_full_contact
    (q : XiZeroCopy) (branch : Bool) :
    ¬ ∃ mu H Q a b c d : ℂ,
      ArbitraryCompatibleAtMode (parameter q branch) mu a b c d ∧
      mu * H = parameter q branch * (H + Q) ∧
      (arbitraryModeMap a b c d (H, Q)).1 ≠ 0 := by
  rintro ⟨mu, H, Q, a, b, c, d, hcompat, hsource, hne⟩
  exact hne (arbitraryCompatible_source_full_dual_zero
    (parameter q branch) mu a b c d H Q
    (physical_parameter_ne_zero q branch) hcompat hsource)

/-- On a source vertex, the full readout is exactly controlled by the
top-right intertwining defect. No symmetry or compatibility is assumed. -/
theorem source_full_readout_eq_defect
    (lam mu a b c d H Q : ℂ)
    (hsource : mu * H = lam * (H + Q)) :
    lam * (arbitraryModeMap a b c d (H, Q)).1 =
      (lam * a + (mu - lam) * b) * H := by
  dsimp [arbitraryModeMap]
  linear_combination -b * hsource

/-- For symmetric maps the whole intertwining defect is one skew operator,
independent of the native-native coefficient. This is the exact positive
survivor of the compatible-current no-go. -/
theorem symmetric_intertwining_defect
    (lam mu a b d u n : ℂ) :
    arbitraryModeMap a b b d (modeAction lam mu (u, n)) =
      ((modeAdjointAction lam mu (arbitraryModeMap a b b d (u, n))).1 +
          (lam * a + (mu - lam) * b) * n,
       (modeAdjointAction lam mu (arbitraryModeMap a b b d (u, n))).2 -
          (lam * a + (mu - lam) * b) * u) := by
  apply Prod.ext
  · dsimp [arbitraryModeMap, modeAction, modeAdjointAction]
    ring
  · dsimp [arbitraryModeMap, modeAction, modeAdjointAction]
    ring

end
end RHTower.D4BMPWFullNativeAdjointSymmetrizer
