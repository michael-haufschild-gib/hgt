import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.LeftRight
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The two-edge trace form and the resolvent dressing of the position anomaly

For the sharp Fourier cutoff `B_a = F^(-1) M_(1_[-a,a]) F` and the position multiplier `X`, the
principal commutator `[X, Q_(0,a)] = -[X, B_a]` is a signed pair of frequency-edge evaluations, and the
exact Sonin projection `Q_a = E - E V B E` has its whole position anomaly factored through that one
distribution.  This module proves the parts of that statement that are algebra or elementary analysis:

* `opComm`, `opComm_mul`, `opComm_inv`, `opComm_bab`, `opComm_twoProjection` — equations `(6c)`–`(6e)`.
  These are **ring identities**: given only that `X` commutes with `A` and with `E`, that `T = B A B`,
  and that `V` is a two-sided inverse of `1 - T`, the position anomaly of `Q_a` is
  `-E V ([X,B] A B V B + B A [X,B] V B + [X,B]) E`.  Every term contains exactly one factor `[X,B]`,
  which is the precise sense in which the Hilbert–Schmidt correction only *dresses* the universal edge
  bundle instead of adding new position defects.
* `edgeTrace`, `edgeTraceForm`, `edgeTraceForm_eq_signature` — equations `(4)` and `(11)`: the boundary
  form is the pullback of the signature matrix `diag(1, -1)` along the two-point edge evaluation.
* `edgeTraceForm_eq_zero_of_even_even`, `edgeTraceForm_eq_zero_of_odd_odd`,
  `edgeTraceForm_of_even_odd` — equation `(12)`: the form vanishes on equal parities and is the pure
  even–odd cross term otherwise.  So it does *not* disappear under parity; it is polarized by it.
* `integral_kernel_commutator` — equation `(6)`: the commutator of position with an integral operator
  has kernel `(x - y) K(x, y)`, the first relative moment.  Nothing about `K` alone controls it.
* `not_continuousAt_sharpCutoff` — equation `(13)`: the sharp cutoff of a function that is continuous
  and nonzero at the edge is discontinuous there.  This is the jump that takes `B_a f` out of the
  position domain.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology MeasureTheory

/-! ## The commutator algebra of the exact two-projection formula -/

section Algebra

variable {R : Type*} [Ring R]

/-- The ring commutator. -/
def opComm (X Y : R) : R := X * Y - Y * X

theorem opComm_mul (X y z : R) : opComm X (y * z) = opComm X y * z + y * opComm X z := by
  rw [opComm, opComm, opComm]
  noncomm_ring

theorem opComm_eq_zero_iff_commute {X Y : R} : opComm X Y = 0 ↔ X * Y = Y * X := by
  rw [opComm, sub_eq_zero]

theorem opComm_sub (X y z : R) : opComm X (y - z) = opComm X y - opComm X z := by
  rw [opComm, opComm, opComm]
  noncomm_ring

/-- **Equation (6d).**  The inverse-commutator identity.  Only the two-sided inverse relations are
used, in the convenient form `T V = V T = V - 1`. -/
theorem opComm_inv {X T V : R} (hVr : T * V = V - 1) (hVl : V * T = V - 1) :
    opComm X V = V * opComm X T * V := by
  rw [opComm, opComm]
  refine Eq.symm ?_
  calc V * (X * T - T * X) * V
      = V * X * (T * V) - (V * T) * X * V := by noncomm_ring
    _ = V * X * (V - 1) - (V - 1) * X * V := by rw [hVr, hVl]
    _ = X * V - V * X := by noncomm_ring

/-- **Equation (6e).**  The commutator of the alternating block `T = B A B`, when `X` commutes with
`A`. -/
theorem opComm_bab {X A B : R} (hA : X * A = A * X) :
    opComm X (B * A * B) = opComm X B * (A * B) + (B * A) * opComm X B := by
  have hzero : opComm X A = 0 := opComm_eq_zero_iff_commute.mpr hA
  rw [opComm_mul, opComm_mul, hzero]
  noncomm_ring

/-- **Equation (6c).**  The exact position anomaly of the two-projection formula
`Q = E - E V B E`.  Every term factors through the single edge commutator `[X, B]`. -/
theorem opComm_twoProjection {X A B E V T Q : R}
    (hA : X * A = A * X) (hE : X * E = E * X) (hT : T = B * A * B)
    (hVr : T * V = V - 1) (hVl : V * T = V - 1) (hQ : Q = E - E * V * B * E) :
    opComm X Q
      = -(E * V * (opComm X B * (A * B) * (V * B) + (B * A) * opComm X B * (V * B)
          + opComm X B) * E) := by
  have hEz : opComm X E = 0 := opComm_eq_zero_iff_commute.mpr hE
  have hVc : opComm X V = V * opComm X T * V := opComm_inv hVr hVl
  have hTc : opComm X T = opComm X B * (A * B) + (B * A) * opComm X B := by
    rw [hT]; exact opComm_bab hA
  have hinner : opComm X (V * B) = V * (opComm X T * (V * B) + opComm X B) := by
    rw [opComm_mul, hVc]
    noncomm_ring
  have hstep : opComm X (E * V * B * E)
      = E * opComm X (V * B) * E := by
    rw [show E * V * B * E = E * (V * B) * E from by noncomm_ring,
      opComm_mul, opComm_mul, hEz]
    noncomm_ring
  have hfirst : opComm X Q = -(E * opComm X (V * B) * E) := by
    rw [hQ, opComm_sub, hEz, hstep, zero_sub]
  rw [hfirst, hinner, hTc]
  noncomm_ring

end Algebra

/-! ## The two-edge trace form -/

/-- The two-point frequency-edge evaluation `Gamma_a`. -/
def edgeTrace (a : ℝ) (F : ℝ → ℂ) : Fin 2 → ℂ
  | 0 => F a
  | 1 => F (-a)

/-- The signature weights of the two-edge form. -/
def edgeSignature : Fin 2 → ℂ
  | 0 => 1
  | 1 => -1

/-- The signed two-edge boundary form of equation `(4)`. -/
def edgeTraceForm (a : ℝ) (F G : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi)) * (F a * (starRingEnd ℂ) (G a) - F (-a) * (starRingEnd ℂ) (G (-a)))

/-- **Equation (11).**  The boundary form is the pullback of the signature matrix `diag(1, -1)` along
the edge evaluation. -/
theorem edgeTraceForm_eq_signature (a : ℝ) (F G : ℝ → ℂ) :
    edgeTraceForm a F G
      = (1 / (2 * Real.pi)) * ∑ j : Fin 2,
          edgeSignature j * edgeTrace a F j * (starRingEnd ℂ) (edgeTrace a G j) := by
  rw [edgeTraceForm]
  simp only [Fin.sum_univ_two, edgeSignature, edgeTrace]
  ring

/-- **Equation (12), equal parities.**  The form vanishes on two even functions. -/
theorem edgeTraceForm_eq_zero_of_even_even {a : ℝ} {F G : ℝ → ℂ}
    (hF : ∀ x, F (-x) = F x) (hG : ∀ x, G (-x) = G x) : edgeTraceForm a F G = 0 := by
  rw [edgeTraceForm, hF a, hG a]
  ring

/-- **Equation (12), equal parities.**  The form vanishes on two odd functions. -/
theorem edgeTraceForm_eq_zero_of_odd_odd {a : ℝ} {F G : ℝ → ℂ}
    (hF : ∀ x, F (-x) = -F x) (hG : ∀ x, G (-x) = -G x) : edgeTraceForm a F G = 0 := by
  rw [edgeTraceForm, hF a, hG a, map_neg]
  ring

/-- **Equation (12).**  On an even–odd pair the form is the pure cross term: logarithmic position
supplies one even and one odd edge coordinate, coupled by a bilateral polarization. -/
theorem edgeTraceForm_of_even_odd {a : ℝ} {F G : ℝ → ℂ}
    (hF : ∀ x, F (-x) = F x) (hG : ∀ x, G (-x) = -G x) :
    edgeTraceForm a F G = (1 / Real.pi) * (F a * (starRingEnd ℂ) (G a)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [edgeTraceForm, hF a, hG a, map_neg]
  field_simp
  ring

/-! ## The first relative moment of the correction kernel -/

/-- **Equation (6).**  The commutator of position with an integral operator has kernel
`(x - y) K(x, y)`.  Hilbert–Schmidt control of `K` says nothing about this weighted kernel. -/
theorem integral_kernel_commutator {K : ℝ → ℝ → ℂ} {f : ℝ → ℂ} (x : ℝ)
    (h1 : Integrable fun y : ℝ => K x y * f y)
    (h2 : Integrable fun y : ℝ => (y : ℂ) * (K x y * f y)) :
    (x : ℂ) * (∫ (y : ℝ), K x y * f y) - ∫ (y : ℝ), K x y * ((y : ℂ) * f y)
      = ∫ (y : ℝ), ((x : ℂ) - (y : ℂ)) * (K x y * f y) := by
  have hcongr : (∫ (y : ℝ), K x y * ((y : ℂ) * f y)) = ∫ (y : ℝ), (y : ℂ) * (K x y * f y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  rw [hcongr, ← integral_const_mul, ← integral_sub (h1.const_mul _) h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

/-! ## Failure of position-domain invariance -/

/-- The sharp frequency cutoff of a function. -/
def sharpCutoff (a : ℝ) (F : ℝ → ℂ) : ℝ → ℂ := fun ξ => if |ξ| ≤ a then F ξ else 0

/-- **Equation (13).**  If `F a ≠ 0` then the sharp cutoff has a jump at the edge.  No regularity of
`F` is needed at all: the cutoff is identically zero just to the right of `a`, while its value at `a`
is `F a`.  This is the jump that takes `B_a f` out of the position domain, and the terms `f` and
`P_a f` have continuous transforms and cannot cancel it. -/
theorem not_continuousAt_sharpCutoff {a : ℝ} {F : ℝ → ℂ} (ha : 0 < a)
    (hFa : F a ≠ 0) : ¬ ContinuousAt (sharpCutoff a F) a := by
  intro hcont
  -- along the right, the cutoff is identically zero
  have hright : Tendsto (sharpCutoff a F) (𝓝[>] a) (𝓝 0) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℂ)) (f := 𝓝[>] a))
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    rw [sharpCutoff]
    have habs : ¬ |ξ| ≤ a := by
      rw [not_le]
      calc a < ξ := hξ
        _ ≤ |ξ| := le_abs_self ξ
    rw [if_neg habs]
  -- but continuity forces the right limit to be the value at the edge
  have hval : sharpCutoff a F a = F a := by
    rw [sharpCutoff, if_pos]
    rw [abs_of_pos ha]
  have hlim : Tendsto (sharpCutoff a F) (𝓝[>] a) (𝓝 (sharpCutoff a F a)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [hval] at hlim
  exact hFa (tendsto_nhds_unique hlim hright)

end GaloisForLFunctions.RHTower

end
