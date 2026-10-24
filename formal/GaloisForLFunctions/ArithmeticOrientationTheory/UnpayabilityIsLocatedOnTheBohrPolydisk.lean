import GaloisForLFunctions.ArithmeticOrientationTheory.UnitsOfTheWienerMonoidPreservePayment
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DoubleZeroKernelsAndLogarithmicSmoothPowerAtThePole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole

/-!
# Unpayability is located on the Bohr polydisk

For a weight `c` with summable mean, the kernels of the critical Wiener algebra that repair `c`,

    P(c) = {k ∈ 𝒲_{1/2} : (Re k) ⋆ c and (Im k) ⋆ c are paid}      (`paidIdeal`),

form an **ideal** of `𝒲_{1/2}`: convolution by critical Wiener kernels preserves payment, and paid
weights with summable means form a vector space.  It contains `δ₁` exactly when `c` is paid
(`one_mem_paidIdeal_iff`).  Gelfand theory then locates every failure of payment:

* **Spectral localization** (`not_receiverBounded_iff_exists_obstruction`): `c` is unpaid iff there
  is a Bohr point `ω` at which every repairing kernel vanishes.  The proper ideal `P(c)` lies in a
  maximal ideal, which is the kernel of a character, which is a Bohr evaluation.
* **The obstruction hull** (`obstructionHull`): the set of such points is nonempty iff `c` is
  unpaid (`obstructionHull_nonempty_iff`), and it is an invariant of the unit orbit:
  `P(u ⋆ c) = P(c)` for every unit `u` of the critical Wiener monoid (`paidIdeal_unit`).
* **The smooth power** (`mem_obstructionHull_smoothPower_iff`): for `0 < ε < ½` the hull of
  `d^{−ε}` is the single half-plane point `s = 1 − ε`, i.e. `ω(p) = p^{ε−1/2}` at every prime:
  the pole law of Trans-Horizon Incidence Mechanics is the statement that the obstruction of the
  smooth power is one point of the spectrum.

The hull is the field's index object for the class "paid": it is empty exactly on the paid class,
it is constant on unit orbits, and the pole laws compute it.
-/

open Finset ArithmeticFunction LSeries

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-! ### Real and imaginary parts of a critical Wiener element -/

/-- The real part of an element of `𝒲_{1/2}`, as a real kernel. -/
def rePart (k : WienerAlgebraAt (1 / 2)) (n : ℕ) : ℝ := (k.toFn n).re

/-- The imaginary part of an element of `𝒲_{1/2}`, as a real kernel. -/
def imPart (k : WienerAlgebraAt (1 / 2)) (n : ℕ) : ℝ := (k.toFn n).im

theorem criticalWiener_of_norm_le {f : ℕ → ℝ} (k : WienerAlgebraAt (1 / 2))
    (hf : ∀ n, |f n| ≤ ‖k.toFn n‖) : CriticalWiener f := by
  refine (summable_norm k).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [norm_term_eq, if_neg hn, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n),
      ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hf n) (by positivity)

theorem criticalWiener_rePart (k : WienerAlgebraAt (1 / 2)) : CriticalWiener (rePart k) :=
  criticalWiener_of_norm_le k fun _ => Complex.abs_re_le_norm _

theorem criticalWiener_imPart (k : WienerAlgebraAt (1 / 2)) : CriticalWiener (imPart k) :=
  criticalWiener_of_norm_le k fun _ => Complex.abs_im_le_norm _

theorem rePart_mul (g k : WienerAlgebraAt (1 / 2)) (n : ℕ) :
    rePart (g * k) n = RHTower.dirichletConv (rePart g) (rePart k) n -
      RHTower.dirichletConv (imPart g) (imPart k) n := by
  unfold rePart imPart RHTower.dirichletConv
  rw [toFn_mul, mul_apply, Complex.re_sum]
  simp_rw [Complex.mul_re]
  rw [sum_sub_distrib, Nat.sum_divisorsAntidiagonal (fun i j => (g.toFn i).re * (k.toFn j).re),
    Nat.sum_divisorsAntidiagonal (fun i j => (g.toFn i).im * (k.toFn j).im)]

theorem imPart_mul (g k : WienerAlgebraAt (1 / 2)) (n : ℕ) :
    imPart (g * k) n = RHTower.dirichletConv (rePart g) (imPart k) n +
      RHTower.dirichletConv (imPart g) (rePart k) n := by
  unfold rePart imPart RHTower.dirichletConv
  rw [toFn_mul, mul_apply, Complex.im_sum]
  simp_rw [Complex.mul_im]
  rw [sum_add_distrib, Nat.sum_divisorsAntidiagonal (fun i j => (g.toFn i).re * (k.toFn j).im),
    Nat.sum_divisorsAntidiagonal (fun i j => (g.toFn i).im * (k.toFn j).re)]

theorem dirichletConv_sub_left' (a b c : ℕ → ℝ) :
    RHTower.dirichletConv (fun n => a n - b n) c =
      fun n => RHTower.dirichletConv a c n - RHTower.dirichletConv b c n := by
  funext n
  unfold RHTower.dirichletConv
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

theorem dirichletConv_add_left' (a b c : ℕ → ℝ) :
    RHTower.dirichletConv (fun n => a n + b n) c =
      fun n => RHTower.dirichletConv a c n + RHTower.dirichletConv b c n := by
  funext n
  unfold RHTower.dirichletConv
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

theorem receiverBounded_zero : ReceiverBounded fun _ : ℕ => (0 : ℝ) :=
  ⟨0, fun T => by simp [weightPronicEnergy, weightCenteredPrefix]⟩

theorem dirichletConv_zero_left (c : ℕ → ℝ) :
    RHTower.dirichletConv (fun _ => (0 : ℝ)) c = fun _ => 0 := by
  funext n; simp [RHTower.dirichletConv]

/-! ### The ideal of repairing kernels -/

section Ideal

variable (c : ℕ → ℝ)

/-- Convolution by a critical Wiener kernel keeps a paid weight paid. -/
theorem paid_conv (hc : Summable fun d : ℕ => |c d / d|) {g : ℕ → ℝ} (hg : CriticalWiener g)
    {k : ℕ → ℝ} (hk : CriticalWiener k) (hpk : ReceiverBounded (RHTower.dirichletConv k c)) :
    ReceiverBounded (RHTower.dirichletConv g (RHTower.dirichletConv k c)) :=
  receiverBounded_dirichletConv hg (summable_abs_dirichletConv_div hk hc) hpk

theorem summable_conv_div (hc : Summable fun d : ℕ => |c d / d|) {g k : ℕ → ℝ}
    (hg : CriticalWiener g) (hk : CriticalWiener k) :
    Summable fun d : ℕ => RHTower.dirichletConv g (RHTower.dirichletConv k c) d / d :=
  (summable_abs_dirichletConv_div hg (summable_abs_dirichletConv_div hk hc)).of_abs

/-- The two parts of a sum of repairing kernels repair. -/
theorem paid_add (hc : Summable fun d : ℕ => |c d / d|) {k l : WienerAlgebraAt (1 / 2)}
    (hk : ReceiverBounded (RHTower.dirichletConv (rePart k) c) ∧
      ReceiverBounded (RHTower.dirichletConv (imPart k) c))
    (hl : ReceiverBounded (RHTower.dirichletConv (rePart l) c) ∧
      ReceiverBounded (RHTower.dirichletConv (imPart l) c)) :
    ReceiverBounded (RHTower.dirichletConv (rePart (k + l)) c) ∧
      ReceiverBounded (RHTower.dirichletConv (imPart (k + l)) c) := by
  have h0 : rePart (k + l) = fun n => rePart k n + rePart l n :=
    funext fun n => by simp [rePart, toFn_add]
  have h1 : imPart (k + l) = fun n => imPart k n + imPart l n :=
    funext fun n => by simp [imPart, toFn_add]
  rw [h0, h1, dirichletConv_add_left', dirichletConv_add_left']
  exact ⟨receiverBounded_add (summable_abs_dirichletConv_div (criticalWiener_rePart k) hc).of_abs
      (summable_abs_dirichletConv_div (criticalWiener_rePart l) hc).of_abs hk.1 hl.1,
    receiverBounded_add (summable_abs_dirichletConv_div (criticalWiener_imPart k) hc).of_abs
      (summable_abs_dirichletConv_div (criticalWiener_imPart l) hc).of_abs hk.2 hl.2⟩

/-- A multiple of a repairing kernel repairs. -/
theorem paid_mul (hc : Summable fun d : ℕ => |c d / d|) (g : WienerAlgebraAt (1 / 2))
    {k : WienerAlgebraAt (1 / 2)}
    (hk : ReceiverBounded (RHTower.dirichletConv (rePart k) c) ∧
      ReceiverBounded (RHTower.dirichletConv (imPart k) c)) :
    ReceiverBounded (RHTower.dirichletConv (rePart (g * k)) c) ∧
      ReceiverBounded (RHTower.dirichletConv (imPart (g * k)) c) := by
  have hgr := criticalWiener_rePart g
  have hgi := criticalWiener_imPart g
  have hkr := criticalWiener_rePart k
  have hki := criticalWiener_imPart k
  have e0 : rePart (g * k) = fun n => RHTower.dirichletConv (rePart g) (rePart k) n -
      RHTower.dirichletConv (imPart g) (imPart k) n := funext (rePart_mul g k)
  have e1 : imPart (g * k) = fun n => RHTower.dirichletConv (rePart g) (imPart k) n +
      RHTower.dirichletConv (imPart g) (rePart k) n := funext (imPart_mul g k)
  rw [e0, e1, dirichletConv_sub_left', dirichletConv_add_left', dirichletConv_assoc,
    dirichletConv_assoc, dirichletConv_assoc, dirichletConv_assoc]
  exact ⟨receiverBounded_sub (summable_conv_div c hc hgr hkr) (summable_conv_div c hc hgi hki)
      (paid_conv c hc hgr hkr hk.1) (paid_conv c hc hgi hki hk.2),
    receiverBounded_add (summable_conv_div c hc hgr hki) (summable_conv_div c hc hgi hkr)
      (paid_conv c hc hgr hki hk.2) (paid_conv c hc hgi hkr hk.1)⟩

theorem paid_zero :
    ReceiverBounded (RHTower.dirichletConv (rePart 0) c) ∧
      ReceiverBounded (RHTower.dirichletConv (imPart 0) c) := by
  have h0 : rePart 0 = fun _ => 0 := funext fun n => by simp [rePart, toFn_zero]
  have h1 : imPart 0 = fun _ => 0 := funext fun n => by simp [imPart, toFn_zero]
  rw [h0, h1, dirichletConv_zero_left]
  exact ⟨receiverBounded_zero, receiverBounded_zero⟩

/-- **The repairing kernels of `c`**: both parts of `k` pay `c`. -/
def paidIdeal (hc : Summable fun d : ℕ => |c d / d|) : Ideal (WienerAlgebraAt (1 / 2)) where
  carrier := {k | ReceiverBounded (RHTower.dirichletConv (rePart k) c) ∧
    ReceiverBounded (RHTower.dirichletConv (imPart k) c)}
  zero_mem' := paid_zero c
  add_mem' hk hl := paid_add c hc hk hl
  smul_mem' g _ hk := paid_mul c hc g hk

theorem mem_paidIdeal (hc : Summable fun d : ℕ => |c d / d|) {k : WienerAlgebraAt (1 / 2)} :
    k ∈ paidIdeal c hc ↔ ReceiverBounded (RHTower.dirichletConv (rePart k) c) ∧
      ReceiverBounded (RHTower.dirichletConv (imPart k) c) := Iff.rfl

/-- `δ₁` repairs `c` iff `c` is paid. -/
theorem one_mem_paidIdeal_iff (hc : Summable fun d : ℕ => |c d / d|) : (1 : WienerAlgebraAt (1 / 2)) ∈ paidIdeal c hc ↔ ReceiverBounded c := by
  have h0 : rePart 1 = unitKernel := funext fun n => by
    simp only [rePart, toFn_one, one_apply, unitKernel]
    split_ifs <;> simp
  have h1 : imPart 1 = fun _ => 0 := funext fun n => by
    simp only [imPart, toFn_one, one_apply]
    split_ifs <;> simp
  rw [mem_paidIdeal c hc, h0, h1, dirichletConv_zero_left]
  have h2 : ReceiverBounded (RHTower.dirichletConv unitKernel c) ↔ ReceiverBounded c :=
    receiverBounded_congr fun n hn => dirichletConv_unitKernel c hn.ne'
  rw [h2]
  exact ⟨fun h => h.1, fun h => ⟨h, receiverBounded_zero⟩⟩

/-! ### Spectral localization -/

/-- The obstruction hull of `c`: the Bohr points at which every repairing kernel vanishes. -/
def obstructionHull (hc : Summable fun d : ℕ => |c d / d|) : Set BohrPoint :=
  {ω | ∀ k ∈ paidIdeal c hc, bohrEval (1 / 2) k.toFn ω = 0}

/-- **Unpayability is located on the Bohr polydisk**: `c` is unpaid iff some Bohr point annihilates
every kernel that repairs it. -/
theorem not_receiverBounded_iff_exists_obstruction (hc : Summable fun d : ℕ => |c d / d|) :
    ¬ ReceiverBounded c ↔ ∃ ω : BohrPoint, ∀ k ∈ paidIdeal c hc, bohrEval (1 / 2) k.toFn ω = 0 := by
  constructor
  · intro hnot
    have hne : paidIdeal c hc ≠ ⊤ := fun h =>
      hnot ((one_mem_paidIdeal_iff c hc).1 (h ▸ Submodule.mem_top))
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal _ hne
    haveI := hM
    refine ⟨characterBohrPoint M.toCharacterSpace, fun k hk => ?_⟩
    rw [← apply_eq_bohrEval]
    exact M.toCharacterSpace_apply_eq_zero_of_mem (hPM hk)
  · rintro ⟨ω, hω⟩ hpaid
    have h := hω 1 ((one_mem_paidIdeal_iff c hc).2 hpaid)
    rw [toFn_one, bohrEval_one] at h
    exact one_ne_zero h

/-- **The hull is empty exactly on the paid class.** -/
theorem obstructionHull_nonempty_iff (hc : Summable fun d : ℕ => |c d / d|) :
    (obstructionHull c hc).Nonempty ↔ ¬ ReceiverBounded c :=
  (not_receiverBounded_iff_exists_obstruction c hc).symm

/-- **The repairing ideal is an invariant of the unit orbit.** -/
theorem paidIdeal_unit (hc : Summable fun d : ℕ => |c d / d|) {u : ℕ → ℝ} (hu : IsWienerUnit u) :
    paidIdeal (RHTower.dirichletConv u c) (summable_abs_dirichletConv_div hu.1 hc) =
      paidIdeal c hc := by
  ext k
  rw [mem_paidIdeal _ _, mem_paidIdeal c hc]
  have key : ∀ f : ℕ → ℝ, CriticalWiener f →
      (ReceiverBounded (RHTower.dirichletConv f (RHTower.dirichletConv u c)) ↔
        ReceiverBounded (RHTower.dirichletConv f c)) := fun f hf => by
    rw [← dirichletConv_assoc, dirichletConv_comm f u, dirichletConv_assoc]
    exact receiverBounded_dirichletConv_iff_of_isWienerUnit hu (summable_abs_dirichletConv_div hf hc)
  rw [key _ (criticalWiener_rePart k), key _ (criticalWiener_imPart k)]

theorem obstructionHull_unit (hc : Summable fun d : ℕ => |c d / d|) {u : ℕ → ℝ} (hu : IsWienerUnit u) :
    obstructionHull (RHTower.dirichletConv u c) (summable_abs_dirichletConv_div hu.1 hc) =
      obstructionHull c hc := by
  unfold obstructionHull
  rw [paidIdeal_unit c hc hu]

end Ideal

/-! ### The obstruction of the smooth power is one point -/

/-- The real part of the Dirichlet series of an element at a real point is the series of its real
part. -/
theorem re_lSeries_real (k : WienerAlgebraAt (1 / 2)) {s : ℝ} (hs : 1 / 2 ≤ s) :
    (LSeries (⇑k.toFn) s).re = ∑' j : ℕ, rePart k j * (j : ℝ) ^ (-s) := by
  have hsum : LSeriesSummable (⇑k.toFn) s :=
    k.summable.of_re_le_re (by simpa using hs)
  unfold LSeries
  rw [Complex.re_tsum hsum]
  refine tsum_congr fun j => ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp [rePart]
  · rw [term_of_ne_zero hj, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg j),
      Complex.div_ofReal_re, Real.rpow_neg (Nat.cast_nonneg j), div_eq_mul_inv]
    rfl

theorem im_lSeries_real (k : WienerAlgebraAt (1 / 2)) {s : ℝ} (hs : 1 / 2 ≤ s) :
    (LSeries (⇑k.toFn) s).im = ∑' j : ℕ, imPart k j * (j : ℝ) ^ (-s) := by
  have hsum : LSeriesSummable (⇑k.toFn) s :=
    k.summable.of_re_le_re (by simpa using hs)
  unfold LSeries
  rw [Complex.im_tsum hsum]
  refine tsum_congr fun j => ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp [imPart]
  · rw [term_of_ne_zero hj, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg j),
      Complex.div_ofReal_im, Real.rpow_neg (Nat.cast_nonneg j), div_eq_mul_inv]
    rfl

theorem summable_abs_smoothPower_div {ε : ℝ} (hε : 0 < ε) :
    Summable fun d : ℕ => |dampedSignWeight unitSign ε d / d| :=
  (summable_unit_weight hε).abs

/-- The pole point `s = 1 − ε` of the smooth power, as a Bohr point. -/
def polePoint (ε : ℝ) (hε2 : ε ≤ 1 / 2) : BohrPoint :=
  halfPlanePoint (1 / 2) ((1 - ε : ℝ) : ℂ) (by simp; linarith)

/-- **The repairing ideal of the smooth power is the maximal ideal of its pole point.** -/
theorem mem_paidIdeal_smoothPower_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (k : WienerAlgebraAt (1 / 2)) :
    k ∈ paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) ↔
      bohrEval (1 / 2) k.toFn (polePoint ε hε2.le) = 0 := by
  rw [mem_paidIdeal _ _, receiverBounded_dirichletConv_unit_iff_critical hε hε2 (criticalWiener_rePart k),
    receiverBounded_dirichletConv_unit_iff_critical hε hε2 (criticalWiener_imPart k), polePoint,
    bohrEval_halfPlanePoint, Complex.ext_iff, re_lSeries_real k (by linarith),
    im_lSeries_real k (by linarith)]
  simp

/-- Two Bohr points that agree at every prime agree at every positive integer. -/
theorem BohrPoint.eq_of_primes {ω ω' : BohrPoint} (h : ∀ p : ℕ, p.Prime → ω.ω p = ω'.ω p) :
    ∀ n : ℕ, n ≠ 0 → ω.ω n = ω'.ω n := by
  intro n
  induction n using Nat.recOnMul with
  | zero => exact fun h0 => absurd rfl h0
  | one => exact fun _ => by rw [ω.map_one, ω'.map_one]
  | prime p hp => exact fun _ => h p hp
  | mul a b ha hb =>
    intro hab
    rw [ω.map_mul, ω'.map_mul, ha (left_ne_zero_of_mul hab), hb (right_ne_zero_of_mul hab)]

/-- The Bohr evaluation reads a Bohr point only at the positive integers. -/
theorem bohrEval_congr {σ : ℝ} (f : ArithmeticFunction ℂ) {ω ω' : BohrPoint}
    (h : ∀ n : ℕ, n ≠ 0 → ω.ω n = ω'.ω n) : bohrEval σ f ω = bohrEval σ f ω' := by
  unfold bohrEval LSeries
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, term_of_ne_zero hn, h n hn]

/-- **The obstruction of the smooth power is its pole point**: for `0 < ε < ½` a Bohr point lies in
the hull of `d^{−ε}` iff `ω(p) = p^{ε − 1/2}` at every prime, i.e. iff it is the half-plane point
`s = 1 − ε`. -/
theorem mem_obstructionHull_smoothPower_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (ω : BohrPoint) :
    ω ∈ obstructionHull (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) ↔
      ∀ p : ℕ, p.Prime → ω.ω p = (polePoint ε hε2.le).ω p := by
  constructor
  · intro hω p hp
    -- the kernel `δ_p − p^{ε−1} δ₁` repairs the smooth power
    set a : ℂ := (polePoint ε hε2.le).ω p / (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
    have hk : (pointMass p - a • 1 : WienerAlgebraAt (1 / 2)) ∈
        paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) := by
      rw [mem_paidIdeal_smoothPower_iff hε hε2, ← bohrCharacter_apply, map_sub, map_smul, map_one,
        bohrCharacter_apply, toFn_pointMass, bohrEval_pointMass hp.ne_zero, smul_eq_mul, mul_one]
      exact sub_self _
    have h := hω _ hk
    rw [← bohrCharacter_apply, map_sub, map_smul, map_one, bohrCharacter_apply, toFn_pointMass,
      bohrEval_pointMass hp.ne_zero, smul_eq_mul, mul_one, sub_eq_zero] at h
    have hp0 : (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h' => hp.ne_zero (by exact_mod_cast h'.1)
    exact (div_left_inj' hp0).1 h
  · intro h k hk
    rw [bohrEval_congr k.toFn (BohrPoint.eq_of_primes h)]
    exact (mem_paidIdeal_smoothPower_iff hε hε2 k).1 hk

end

end GaloisForLFunctions.ArithmeticOrientationTheory
