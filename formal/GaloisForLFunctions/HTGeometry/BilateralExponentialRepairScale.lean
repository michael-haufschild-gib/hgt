import GaloisForLFunctions.HTGeometry.BilateralExponentialConvolutionAlgebra
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Bilateral exponential repair scale

On the Banach convolution algebras `𝒜_a`:

* the exponential reporter `χ_z(x) = ∑ x_k e^{zk}` is a continuous character exactly on the strip
  `|Re z| ≤ a`, where it has norm one; every character is such a reporter, so the character space
  is the annulus `e^{-a} ≤ |w| ≤ e^{a}` in `w = e^z`;
* reflection and phase are isometries acting on reporters by `z ↦ -z`, `z ↦ z - it`;
* the horizontal intervention `(T_c x)_k = e^{ck} x_k` maps `𝒜_{a+|c|} → 𝒜_a` with norm one,
  sends `χ_z` to `χ_{z+c}`, is unbounded on every fixed `𝒜_a` when `c ≠ 0`, and the loss `|c|` is
  sharp.
-/

namespace GaloisForLFunctions.HTGeometry.BilateralRepair

noncomputable section

open Filter Topology

namespace Fibre

variable {a : ℝ} [ha : Fact (0 ≤ a)]

instance : NormOneClass (Fibre a) := ⟨norm_one_eq⟩

/-- The atom `δ_k ∈ 𝒜_a`. -/
def atom (k : ℤ) : Fibre a := mk (atomSeq k) (admissible_atomSeq a k)

omit ha in
@[simp] theorem seq_atom (k : ℤ) : (atom k : Fibre a).seq = atomSeq k := rfl

theorem norm_atom (k : ℤ) : ‖(atom k : Fibre a)‖ = expWeight a k := wnorm_atomSeq a k

theorem atomSeq_conv (j m : ℤ) : conv (atomSeq j) (atomSeq m) = atomSeq (j + m) := by
  funext n
  unfold conv
  rw [tsum_eq_single j]
  · by_cases h : n = j + m
    · subst h; simp [atomSeq]
    · have : n - j ≠ m := fun h' => h (by rw [← h']; ring)
      simp [atomSeq, this, h]
  · intro i hi; simp [atomSeq, hi]

theorem atom_mul (j m : ℤ) : (atom j : Fibre a) * atom m = atom (j + m) :=
  ext (by simp [atomSeq_conv])

omit ha in
theorem atom_zero [Fact (0 ≤ a)] : (atom 0 : Fibre a) = 1 := ext (by
  funext k; simp [atomSeq, unitSeq])

/-- Coordinate evaluation `x ↦ x_k` as a continuous linear functional. -/
def coord (k : ℤ) : Fibre a →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x.seq k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    fun x => by rw [one_mul]; exact x.admissible.norm_le ha.out k

@[simp] theorem coord_apply (k : ℤ) (x : Fibre a) : coord k x = x.seq k := rfl

/-- Every element is the norm-convergent sum of its atoms. -/
theorem hasSum_atoms (x : Fibre a) : HasSum (fun k => x.seq k • (atom k : Fibre a)) x := by
  have hsum : Summable fun k => x.seq k • (atom k : Fibre a) := by
    refine Summable.of_norm (x.admissible.congr fun k => ?_)
    rw [norm_smul, norm_atom, mul_comm]
  refine (hsum.hasSum_iff).mpr (ext (funext fun j => ?_))
  have h := (coord j).map_tsum hsum
  simp only [coord_apply] at h
  rw [h, tsum_eq_single j]
  · simp [atomSeq]
  · intro k hk; simp [atomSeq, Ne.symm hk]

/-! ## Exponential reporters -/

/-- The reporter `χ_z` as an algebra homomorphism on the strip `|Re z| ≤ a`. -/
def reporterHom (z : ℂ) (hz : |z.re| ≤ a) : Fibre a →ₐ[ℂ] ℂ where
  toFun x := reporter z x.seq
  map_one' := reporter_unitSeq z
  map_mul' x y := reporter_conv hz x.admissible y.admissible
  map_zero' := by simp [reporter]
  map_add' x y := by
    simp only [reporter, seq_add, Pi.add_apply, add_mul]
    exact Summable.tsum_add (summable_reporter hz x.admissible) (summable_reporter hz y.admissible)
  commutes' c := by
    change reporter z (c • (1 : Fibre a)).seq = c
    simp only [seq_smul, seq_one, reporter, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [tsum_mul_left]
    have := reporter_unitSeq z
    rw [reporter] at this
    rw [this, mul_one]

theorem reporterHom_apply (z : ℂ) (hz : |z.re| ≤ a) (x : Fibre a) :
    reporterHom z hz x = reporter z x.seq := rfl

/-- The reporter as a continuous linear functional of norm one. -/
def reporterCLM (z : ℂ) (hz : |z.re| ≤ a) : Fibre a →L[ℂ] ℂ :=
  LinearMap.mkContinuous (reporterHom z hz).toLinearMap 1
    fun x => by rw [one_mul]; exact norm_reporter_le hz x.admissible

theorem reporterCLM_apply (z : ℂ) (hz : |z.re| ≤ a) (x : Fibre a) :
    reporterCLM z hz x = reporter z x.seq := rfl

/-- **Theorem 2.2** In the strip the reporter has norm exactly one. -/
theorem norm_reporterCLM (z : ℂ) (hz : |z.re| ≤ a) : ‖reporterCLM z hz‖ = 1 := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) ?_
  have h := (reporterCLM z hz).le_opNorm 1
  rw [reporterCLM_apply, seq_one, reporter_unitSeq, norm_one, norm_one, mul_one] at h
  exact h

/-- **(BER.7)** The reporter ratio on atoms is `e^{bk - a|k|}`, `b = Re z`. -/
theorem reporter_atom_ratio (z : ℂ) (k : ℤ) :
    ‖reporterCoeff z k‖ / ‖(atom k : Fibre a)‖ = Real.exp (z.re * k - a * |(k : ℝ)|) := by
  rw [norm_reporterCoeff, norm_atom, expWeight, ← Real.exp_sub]

/-- **Theorem 2.2** `χ_z` extends to a continuous functional on `𝒜_a` exactly on the strip. -/
theorem exists_reporter_clm_iff (z : ℂ) :
    (∃ φ : Fibre a →L[ℂ] ℂ, ∀ k, φ (atom k) = reporterCoeff z k) ↔ |z.re| ≤ a := by
  constructor
  · rintro ⟨φ, hφ⟩
    by_contra hz
    rw [not_le] at hz
    have hbound : ∀ k : ℤ, Real.exp (z.re * k) ≤ ‖φ‖ * expWeight a k := fun k => by
      rw [← norm_reporterCoeff, ← hφ, ← norm_atom]
      exact φ.le_opNorm _
    rcases lt_abs.mp hz with hpos | hneg
    · -- `Re z > a`: follow positive atoms
      have hgap : 0 < z.re - a := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (‖φ‖ / (z.re - a))
      have h := hbound n
      rw [expWeight, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℤ))] at h
      push_cast at h
      have hexp : Real.exp (z.re * n) = Real.exp ((z.re - a) * n) * Real.exp (a * n) := by
        rw [← Real.exp_add]; ring_nf
      rw [hexp] at h
      have hle : Real.exp ((z.re - a) * n) ≤ ‖φ‖ :=
        le_of_mul_le_mul_right h (Real.exp_pos _)
      have hlin : (z.re - a) * n + 1 ≤ Real.exp ((z.re - a) * n) := Real.add_one_le_exp _
      have : ‖φ‖ < (z.re - a) * n := by
        rw [div_lt_iff₀ hgap] at hn; linarith
      linarith
    · -- `Re z < -a`: follow negative atoms
      have hgap : 0 < -z.re - a := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (‖φ‖ / (-z.re - a))
      have h := hbound (-(n : ℤ))
      rw [expWeight] at h
      push_cast at h
      rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)] at h
      have hexp : Real.exp (z.re * -n) = Real.exp ((-z.re - a) * n) * Real.exp (a * n) := by
        rw [← Real.exp_add]; ring_nf
      rw [hexp] at h
      have hle : Real.exp ((-z.re - a) * n) ≤ ‖φ‖ :=
        le_of_mul_le_mul_right h (Real.exp_pos _)
      have hlin : (-z.re - a) * n + 1 ≤ Real.exp ((-z.re - a) * n) := Real.add_one_le_exp _
      have : ‖φ‖ < (-z.re - a) * n := by
        rw [div_lt_iff₀ hgap] at hn; linarith
      linarith
  · intro hz
    exact ⟨reporterCLM z hz, fun k => by
      rw [reporterCLM_apply, seq_atom, reporter_atomSeq]⟩

omit ha in
/-- **(BER.8)** In `w = e^z` the strip is the closed annulus `e^{-a} ≤ |w| ≤ e^a`. -/
theorem abs_re_le_iff_annulus (z : ℂ) :
    |z.re| ≤ a ↔ Real.exp (-a) ≤ ‖Complex.exp z‖ ∧ ‖Complex.exp z‖ ≤ Real.exp a := by
  rw [Complex.norm_exp, Real.exp_le_exp, Real.exp_le_exp, abs_le]

/-- **Character space.**  Every character of `𝒜_a` is an exponential reporter from the strip. -/
theorem exists_reporter_of_algHom (φ : Fibre a →ₐ[ℂ] ℂ) :
    ∃ (z : ℂ) (hz : |z.re| ≤ a), φ = reporterHom z hz := by
  set w := φ (atom 1) with hw
  have hunit : w * φ (atom (-1)) = 1 := by
    rw [hw, ← map_mul, atom_mul, show (1 : ℤ) + -1 = 0 by norm_num, atom_zero, map_one]
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hunit
  have hbound : ∀ x : Fibre a, ‖φ x‖ ≤ ‖x‖ :=
    fun x => spectrum.norm_le_norm_of_mem (AlgHom.apply_mem_spectrum φ x)
  set z := Complex.log w with hzdef
  have hexpz : Complex.exp z = w := Complex.exp_log hw0
  have hz : |z.re| ≤ a := by
    rw [abs_re_le_iff_annulus, hexpz]
    constructor
    · have h1 := hbound (atom (-1))
      rw [norm_atom, expWeight] at h1
      have hinv : φ (atom (-1)) = w⁻¹ := eq_inv_of_mul_eq_one_right hunit
      rw [hinv, norm_inv] at h1
      push_cast at h1
      simp only [abs_neg, abs_one, mul_one] at h1
      rw [Real.exp_neg]
      exact (inv_le_comm₀ (norm_pos_iff.mpr hw0) (Real.exp_pos a)).mp h1
    · have h1 := hbound (atom 1)
      rw [norm_atom, expWeight] at h1
      push_cast at h1
      simpa using h1
  refine ⟨z, hz, ?_⟩
  have hatom : ∀ k : ℤ, φ (atom k) = reporterCoeff z k := by
    intro k
    induction k using Int.induction_on with
    | zero => rw [atom_zero, map_one]; simp [reporterCoeff]
    | succ n ih =>
      rw [← atom_mul, map_mul, ih, reporterCoeff_add, ← hw]
      congr 1
      rw [reporterCoeff, Int.cast_one, mul_one, hexpz]
    | pred n ih =>
      have h : φ (atom (-(n : ℤ))) * φ (atom (-1)) =
          reporterCoeff z (-(n : ℤ)) * φ (atom (-1)) := by rw [ih]
      rw [← map_mul, atom_mul, show -(n : ℤ) + -1 = -(n : ℤ) - 1 by ring] at h
      rw [h, show -(n : ℤ) - 1 = -(n : ℤ) + -1 by ring, reporterCoeff_add]
      congr 1
      rw [eq_inv_of_mul_eq_one_right hunit, ← hexpz, reporterCoeff]
      push_cast
      rw [mul_neg_one, Complex.exp_neg]
  refine AlgHom.ext fun x => ?_
  have hsum := hasSum_atoms x
  have hφ : Continuous φ := by
    refine AddMonoidHomClass.continuous_of_bound φ 1 fun y => ?_
    rw [one_mul]; exact hbound y
  have h1 := hsum.map φ hφ
  simp only [Function.comp_def, map_smul, hatom, smul_eq_mul] at h1
  rw [reporterHom_apply, reporter]
  exact h1.tsum_eq.symm

end Fibre

/-! ## Reflection and phase -/

/-- Reflection `(R x)_k = x_{-k}`. -/
def reflectSeq (x : ℤ → ℂ) : ℤ → ℂ := fun k => x (-k)

theorem admissible_reflectSeq {a : ℝ} {x : ℤ → ℂ} (hx : Admissible a x) :
    Admissible a (reflectSeq x) := by
  have := ((Equiv.neg ℤ).summable_iff).mpr hx
  refine this.congr fun k => ?_
  simp [reflectSeq, expWeight_neg]

theorem wnorm_reflectSeq (a : ℝ) (x : ℤ → ℂ) : wnorm a (reflectSeq x) = wnorm a x := by
  rw [wnorm, wnorm, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun k => ?_
  simp [reflectSeq, expWeight_neg]

/-- **(BER.10)** `χ_z(R x) = χ_{-z}(x)`. -/
theorem reporter_reflectSeq (z : ℂ) (x : ℤ → ℂ) : reporter z (reflectSeq x) = reporter (-z) x := by
  rw [reporter, reporter, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun k => ?_
  simp [reflectSeq, reporterCoeff]

/-- Phase `(U_t x)_k = e^{-itk} x_k`. -/
def phaseSeq (t : ℝ) (x : ℤ → ℂ) : ℤ → ℂ := fun k => Complex.exp (-(t * Complex.I * k)) * x k

theorem norm_phaseSeq (t : ℝ) (x : ℤ → ℂ) (k : ℤ) : ‖phaseSeq t x k‖ = ‖x k‖ := by
  rw [phaseSeq, norm_mul, Complex.norm_exp]
  simp [Complex.mul_re]

theorem admissible_phaseSeq {a : ℝ} (t : ℝ) {x : ℤ → ℂ} (hx : Admissible a x) :
    Admissible a (phaseSeq t x) := hx.congr fun k => by rw [norm_phaseSeq]

theorem wnorm_phaseSeq (a t : ℝ) (x : ℤ → ℂ) : wnorm a (phaseSeq t x) = wnorm a x := by
  simp only [wnorm, norm_phaseSeq]

/-- **(BER.10)** `χ_z(U_t x) = χ_{z - it}(x)`. -/
theorem reporter_phaseSeq (z : ℂ) (t : ℝ) (x : ℤ → ℂ) :
    reporter z (phaseSeq t x) = reporter (z - t * Complex.I) x := by
  rw [reporter, reporter]
  refine tsum_congr fun k => ?_
  simp only [phaseSeq, reporterCoeff]
  rw [mul_comm (Complex.exp _) (x k), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- **(BER.17)** Phase observation is periodic: `U_{t+2π} = U_t`. -/
theorem phaseSeq_add_two_pi (t : ℝ) (x : ℤ → ℂ) : phaseSeq (t + 2 * Real.pi) x = phaseSeq t x := by
  funext k
  simp only [phaseSeq]
  congr 1
  have h := Complex.exp_int_mul_two_pi_mul_I (-k)
  rw [show -(((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I * k) =
      -((t : ℂ) * Complex.I * k) + (-k : ℤ) * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_add, h, mul_one]

/-! ## Horizontal intervention -/

/-- Horizontal intervention `(T_c x)_k = e^{ck} x_k`. -/
def tiltSeq (c : ℝ) (x : ℤ → ℂ) : ℤ → ℂ := fun k => (Real.exp (c * k) : ℂ) * x k

theorem expWeight_mul_exp_le {a b c : ℝ} (hb : a + |c| ≤ b) (k : ℤ) :
    expWeight a k * Real.exp (c * k) ≤ expWeight b k := by
  rw [expWeight, expWeight, ← Real.exp_add, Real.exp_le_exp]
  have h1 : c * k ≤ |c| * |(k : ℝ)| := by
    rw [← abs_mul]; exact le_abs_self _
  nlinarith [abs_nonneg (k : ℝ)]

theorem norm_tiltSeq (c : ℝ) (x : ℤ → ℂ) (k : ℤ) :
    ‖tiltSeq c x k‖ = Real.exp (c * k) * ‖x k‖ := by
  rw [tiltSeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- **(BER.11)** `T_c : 𝒜_b → 𝒜_a` whenever `a + |c| ≤ b`. -/
theorem admissible_tiltSeq {a b c : ℝ} (hb : a + |c| ≤ b) {x : ℤ → ℂ} (hx : Admissible b x) :
    Admissible a (tiltSeq c x) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _))
    (fun k => by
      rw [norm_tiltSeq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (expWeight_mul_exp_le hb k) (norm_nonneg _)) hx

theorem wnorm_tiltSeq_le {a b c : ℝ} (hb : a + |c| ≤ b) {x : ℤ → ℂ} (hx : Admissible b x) :
    wnorm a (tiltSeq c x) ≤ wnorm b x :=
  Summable.tsum_le_tsum (fun k => by
      rw [norm_tiltSeq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (expWeight_mul_exp_le hb k) (norm_nonneg _))
    (admissible_tiltSeq hb hx) hx

/-- **(BER.12)** `χ_z(T_c x) = χ_{z+c}(x)`. -/
theorem reporter_tiltSeq (z : ℂ) (c : ℝ) (x : ℤ → ℂ) :
    reporter z (tiltSeq c x) = reporter (z + c) x := by
  rw [reporter, reporter]
  refine tsum_congr fun k => ?_
  simp only [tiltSeq, reporterCoeff]
  push_cast
  rw [mul_comm ((Complex.exp (c * k))) (x k), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem tiltSeq_atomSeq (c : ℝ) (k : ℤ) : tiltSeq c (atomSeq k) = (Real.exp (c * k) : ℂ) • atomSeq k := by
  funext j
  by_cases h : j = k
  · subst h; simp [tiltSeq, atomSeq]
  · simp [tiltSeq, atomSeq, h]

theorem wnorm_tiltSeq_atomSeq (a c : ℝ) (k : ℤ) :
    wnorm a (tiltSeq c (atomSeq k)) = Real.exp (c * k) * expWeight a k := by
  rw [wnorm, tsum_eq_single k]
  · rw [norm_tiltSeq]; simp [atomSeq]; ring
  · intro j hj; simp [tiltSeq, atomSeq, hj]

/-- **Sharpness of the grade loss.**  If `0 ≤ β < |c|`, `T_c` is not bounded from `𝒜_{a+β}` to
`𝒜_a`; with `β = 0`, `T_c` (`c ≠ 0`) is unbounded on every fixed `𝒜_a`. -/
theorem tiltSeq_loss_sharp (a : ℝ) {c β : ℝ} (hβ : β < |c|) :
    ¬ ∃ C : ℝ, ∀ k : ℤ,
      wnorm a (tiltSeq c (atomSeq k)) ≤ C * wnorm (a + β) (atomSeq k) := by
  rintro ⟨C, hC⟩
  have hgap : 0 < |c| - β := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (|c| - β))
  set k : ℤ := if 0 ≤ c then (n : ℤ) else -(n : ℤ) with hk
  have hck : c * (k : ℝ) = |c| * n := by
    rw [hk]
    split_ifs with h
    · rw [abs_of_nonneg h]; push_cast; ring
    · rw [abs_of_neg (not_le.mp h)]; push_cast; ring
  have habsk : |(k : ℝ)| = n := by
    rw [hk]; split_ifs <;> push_cast <;> simp
  have h := hC k
  rw [wnorm_tiltSeq_atomSeq, wnorm_atomSeq, expWeight, expWeight, hck, habsk] at h
  have hsplit : Real.exp (|c| * n) * Real.exp (a * n) =
      Real.exp ((|c| - β) * n) * Real.exp ((a + β) * n) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hsplit] at h
  have hle : Real.exp ((|c| - β) * n) ≤ C := le_of_mul_le_mul_right h (Real.exp_pos _)
  have hlin := Real.add_one_le_exp ((|c| - β) * n)
  rw [div_lt_iff₀ hgap] at hn
  linarith

theorem tiltSeq_unbounded (a : ℝ) {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ C : ℝ, ∀ k : ℤ, wnorm a (tiltSeq c (atomSeq k)) ≤ C * wnorm a (atomSeq k) := by
  have h := tiltSeq_loss_sharp a (β := 0) (abs_pos.mpr hc)
  simpa using h

namespace Fibre

variable {a : ℝ} [ha : Fact (0 ≤ a)]

/-- **Theorem 3.1** Reflection as a linear isometry of `𝒜_a`. -/
def reflect : Fibre a →ₗᵢ[ℂ] Fibre a where
  toFun x := mk (reflectSeq x.seq) (admissible_reflectSeq x.admissible)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := wnorm_reflectSeq a x.seq

/-- **Theorem 3.1** Phase as a linear isometry of `𝒜_a`. -/
def phase (t : ℝ) : Fibre a →ₗᵢ[ℂ] Fibre a where
  toFun x := mk (phaseSeq t x.seq) (admissible_phaseSeq t x.admissible)
  map_add' x y := ext (funext fun k => by simp [phaseSeq, mul_add])
  map_smul' c x := ext (funext fun k => by simp [phaseSeq]; ring)
  norm_map' x := wnorm_phaseSeq a t x.seq

theorem reflect_seq (x : Fibre a) : (reflect x).seq = reflectSeq x.seq := rfl

theorem phase_seq (t : ℝ) (x : Fibre a) : (phase t x).seq = phaseSeq t x.seq := rfl

/-- **(BER.17)** `U_{t+2π} = U_t` on every fibre. -/
theorem phase_add_two_pi (t : ℝ) (x : Fibre a) : phase (t + 2 * Real.pi) x = phase t x :=
  ext (phaseSeq_add_two_pi t x.seq)

end Fibre

namespace Fibre

variable {a b : ℝ} [ha : Fact (0 ≤ a)] [hb : Fact (0 ≤ b)]

/-- **Theorem 3.2** The horizontal intervention `T_c : 𝒜_b → 𝒜_a` for `a + |c| ≤ b`. -/
def tilt (c : ℝ) (hab : a + |c| ≤ b) : Fibre b →L[ℂ] Fibre a :=
  LinearMap.mkContinuous
    { toFun := fun x => mk (tiltSeq c x.seq) (admissible_tiltSeq hab x.admissible)
      map_add' := fun x y => ext (funext fun k => by simp [tiltSeq, mul_add])
      map_smul' := fun r x => ext (funext fun k => by simp [tiltSeq]; ring) } 1
    fun x => by rw [one_mul]; exact wnorm_tiltSeq_le hab x.admissible

theorem tilt_seq (c : ℝ) (hab : a + |c| ≤ b) (x : Fibre b) :
    (tilt c hab x).seq = tiltSeq c x.seq := rfl

/-- **Theorem 3.2** `‖T_c : 𝒜_{a+|c|} → 𝒜_a‖ = 1`. -/
theorem norm_tilt (c : ℝ) (hab : a + |c| ≤ b) : ‖tilt c hab‖ = 1 := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) ?_
  have h := (tilt c hab).le_opNorm (1 : Fibre b)
  have h1 : tilt c hab (1 : Fibre b) = 1 := ext (funext fun k => by
    by_cases hk : k = 0
    · subst hk; simp [tilt_seq, tiltSeq, unitSeq]
    · simp [tilt_seq, tiltSeq, unitSeq, hk])
  rw [h1, norm_one_eq, norm_one_eq, mul_one] at h
  exact h

/-- **Theorem 3.2** Reporter exchange `χ_z ∘ T_c = χ_{z+c}` on the strip. -/
theorem reporter_tilt (c : ℝ) (hab : a + |c| ≤ b) (z : ℂ) (hz : |z.re| ≤ a) (x : Fibre b) :
    reporterCLM z hz (tilt c hab x) = reporter (z + c) x.seq := by
  rw [reporterCLM_apply, tilt_seq, reporter_tiltSeq]

/-- The inclusion `𝒜_b ⊆ 𝒜_a` for `a ≤ b`, a norm-one-bounded injective map. -/
def inclusion (hab : a ≤ b) : Fibre b →L[ℂ] Fibre a :=
  LinearMap.mkContinuous
    { toFun := fun x => mk x.seq (Summable.of_nonneg_of_le
          (fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _))
          (fun k => mul_le_mul_of_nonneg_right (expWeight_mono hab k) (norm_nonneg _))
          x.admissible)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    fun x => by
      rw [one_mul]
      exact Summable.tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_right (expWeight_mono hab k) (norm_nonneg _))
        (Summable.of_nonneg_of_le (fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _))
          (fun k => mul_le_mul_of_nonneg_right (expWeight_mono hab k) (norm_nonneg _))
          x.admissible) x.admissible

theorem inclusion_injective (hab : a ≤ b) : Function.Injective (inclusion (a := a) (b := b) hab) :=
  fun x y h => by
    have h' := congrArg seq h
    exact ext h'

end Fibre

/-! ## The strict endogenous repair chain -/

/-- The separating sequence `e^{-m|k|}/(1+|k|)²`. -/
def separatingSeq (m : ℝ) (k : ℤ) : ℂ :=
  ((Real.exp (-(m * |(k : ℝ)|)) / (1 + |(k : ℝ)|) ^ 2 : ℝ) : ℂ)

theorem norm_separatingSeq (m : ℝ) (k : ℤ) :
    ‖separatingSeq m k‖ = Real.exp (-(m * |(k : ℝ)|)) / (1 + |(k : ℝ)|) ^ 2 := by
  rw [separatingSeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem summable_geometric_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℤ => r ^ k.natAbs := by
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨by simpa using summable_geometric_of_lt_one hr0 hr1,
    by simpa using summable_geometric_of_lt_one hr0 hr1⟩

/-- Below the separating grade `m` the sequence is admissible. -/
theorem admissible_separatingSeq {a m : ℝ} (ham : a < m) : Admissible a (separatingSeq m) := by
  have hr : Real.exp (-(m - a)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _))
    (fun k => ?_) (summable_geometric_natAbs (Real.exp_pos _).le hr)
  rw [norm_separatingSeq, expWeight]
  have h1 : (1 : ℝ) ≤ (1 + |(k : ℝ)|) ^ 2 := by nlinarith [abs_nonneg (k : ℝ)]
  calc Real.exp (a * |(k : ℝ)|) * (Real.exp (-(m * |(k : ℝ)|)) / (1 + |(k : ℝ)|) ^ 2)
      ≤ Real.exp (a * |(k : ℝ)|) * Real.exp (-(m * |(k : ℝ)|)) :=
        mul_le_mul_of_nonneg_left (div_le_self (Real.exp_pos _).le h1) (Real.exp_pos _).le
    _ = Real.exp (-(m - a)) ^ k.natAbs := by
        rw [← Real.exp_add, ← Real.exp_nat_mul, Nat.cast_natAbs, Int.cast_abs]
        congr 1; ring

/-- Above the separating grade `m` the sequence is not admissible. -/
theorem not_admissible_separatingSeq {b m : ℝ} (hmb : m < b) :
    ¬ Admissible b (separatingSeq m) := by
  intro h
  have hnat := (summable_int_iff_summable_nat_and_neg.mp h).1
  have ht := hnat.tendsto_atTop_zero
  set δ := b - m with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hlim : Tendsto (fun x : ℝ => (δ * (1 + x)) ^ 2 * Real.exp (-(δ * (1 + x)))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      ((tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop hδ)
  have hev : ∀ᶠ n : ℕ in atTop,
      (δ * (1 + (n : ℝ))) ^ 2 * Real.exp (-(δ * (1 + (n : ℝ)))) < δ ^ 2 * Real.exp (-δ) :=
    (hlim.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ n : ℕ in atTop, expWeight b (n : ℤ) * ‖separatingSeq m (n : ℤ)‖ < 1 :=
    ht.eventually (gt_mem_nhds one_pos)
  obtain ⟨n, h1, h2⟩ := (hev.and hev2).exists
  have hkey : (1 + (n : ℝ)) ^ 2 < Real.exp (δ * n) := by
    have e1 : (δ * (1 + (n : ℝ))) ^ 2 * Real.exp (-(δ * (1 + (n : ℝ)))) =
        δ ^ 2 * Real.exp (-δ) * ((1 + (n : ℝ)) ^ 2 * Real.exp (-(δ * n))) := by
      rw [show -(δ * (1 + (n : ℝ))) = -δ + -(δ * n) by ring, Real.exp_add]; ring
    rw [e1] at h1
    have hpos : 0 < δ ^ 2 * Real.exp (-δ) := by positivity
    have h3 : (1 + (n : ℝ)) ^ 2 * Real.exp (-(δ * n)) < 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)] at h3
    exact h3
  rw [norm_separatingSeq, expWeight] at h2
  push_cast at h2
  rw [abs_of_nonneg (Nat.cast_nonneg n)] at h2
  have hval : Real.exp (b * n) * (Real.exp (-(m * n)) / (1 + (n : ℝ)) ^ 2) =
      Real.exp (δ * n) / (1 + (n : ℝ)) ^ 2 := by
    rw [mul_div_assoc', ← Real.exp_add]; congr 2; rw [hδdef]; ring
  rw [hval, div_lt_one (by positivity)] at h2
  linarith

/-- **Theorem 4.1(5)** The inclusion `𝒜_{(n+1)c} ⊂ 𝒜_{nc}` is strict, witnessed by (BER.15). -/
theorem repairChain_strict {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Admissible (n * c) (separatingSeq ((n + 1 / 2) * c)) ∧
      ¬ Admissible ((n + 1) * c) (separatingSeq ((n + 1 / 2) * c)) :=
  ⟨admissible_separatingSeq (by nlinarith), not_admissible_separatingSeq (by nlinarith)⟩

/-- **Theorem 4.1** Failure generates the next least repair: at stage `a_n = nc`, the reporter
`χ_{a_n}` is admitted; executing `T_c` produces `χ_{a_{n+1}}`, which is not admitted on
`𝒜_{a_n}` but is admitted on `𝒜_{a_{n+1}}`; `T_c : 𝒜_{a_{n+1}} → 𝒜_{a_n}` has norm one; and the
inclusion is strict. -/
theorem repairChain {c : ℝ} (hc : 0 < c) (n : ℕ) :
    haveI : Fact (0 ≤ (n : ℝ) * c) := ⟨by positivity⟩
    haveI : Fact (0 ≤ ((n : ℝ) + 1) * c) := ⟨by positivity⟩
    (∃ φ : Fibre ((n : ℝ) * c) →L[ℂ] ℂ,
        ∀ k, φ (Fibre.atom k) = reporterCoeff (((n : ℝ) * c : ℝ) : ℂ) k) ∧
      (∀ x : ℤ → ℂ, reporter (((n : ℝ) * c : ℝ) : ℂ) (tiltSeq c x) =
        reporter ((((n : ℝ) + 1) * c : ℝ) : ℂ) x) ∧
      ¬ (∃ φ : Fibre ((n : ℝ) * c) →L[ℂ] ℂ,
        ∀ k, φ (Fibre.atom k) = reporterCoeff ((((n : ℝ) + 1) * c : ℝ) : ℂ) k) ∧
      (∃ φ : Fibre (((n : ℝ) + 1) * c) →L[ℂ] ℂ,
        ∀ k, φ (Fibre.atom k) = reporterCoeff ((((n : ℝ) + 1) * c : ℝ) : ℂ) k) ∧
      (∃ h : (n : ℝ) * c + |c| ≤ ((n : ℝ) + 1) * c, ‖Fibre.tilt c h‖ = 1) ∧
      (Admissible (n * c) (separatingSeq ((n + 1 / 2) * c)) ∧
        ¬ Admissible ((n + 1) * c) (separatingSeq ((n + 1 / 2) * c))) := by
  haveI : Fact (0 ≤ (n : ℝ) * c) := ⟨by positivity⟩
  haveI : Fact (0 ≤ ((n : ℝ) + 1) * c) := ⟨by positivity⟩
  have hnc : 0 ≤ (n : ℝ) * c := by positivity
  refine ⟨(Fibre.exists_reporter_clm_iff _).mpr (by simp [abs_of_nonneg hnc]),
    fun x => by rw [reporter_tiltSeq]; push_cast; ring_nf, ?_,
    (Fibre.exists_reporter_clm_iff _).mpr (by simp [abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((n : ℝ) + 1) * c)]),
    ⟨by rw [abs_of_pos hc]; ring_nf; rfl, Fibre.norm_tilt c _⟩, repairChain_strict hc n⟩
  rw [Fibre.exists_reporter_clm_iff]
  simp only [Complex.ofReal_re]
  rw [abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) * c)]
  nlinarith

/-- **Theorem 4.2** Self-catalytic repair: the boundary reporter coefficient squares to the next
one, and executing it as a multiplier produces the next reporter. -/
theorem selfCatalytic (a : ℝ) (k : ℤ) (x : ℤ → ℂ) :
    reporterCoeff (a : ℂ) k ^ 2 = reporterCoeff ((2 * a : ℝ) : ℂ) k ∧
      reporter (a : ℂ) (tiltSeq a x) = reporter ((2 * a : ℝ) : ℂ) x := by
  refine ⟨?_, ?_⟩
  · rw [reporterCoeff, reporterCoeff, ← Complex.exp_nat_mul]; push_cast; ring_nf
  · rw [reporter_tiltSeq]; push_cast; ring_nf

/-- **Theorem 4.2** On the dyadic chain `a_n = 2ⁿ a₀`, the admitted reporter at stage `n` is the
multiplier whose execution generates stage `n+1`; `χ_{a_{n+1}}` is excluded from `𝒜_{a_n}` and
admitted on `𝒜_{a_{n+1}}`, and `S_{a_n} : 𝒜_{a_{n+1}} → 𝒜_{a_n}` has norm one. -/
theorem dyadicRepair {a₀ : ℝ} (ha₀ : 0 < a₀) (n : ℕ) :
    haveI : Fact (0 ≤ 2 ^ n * a₀) := ⟨by positivity⟩
    haveI : Fact (0 ≤ 2 ^ (n + 1) * a₀) := ⟨by positivity⟩
    (∀ k : ℤ, reporterCoeff ((2 ^ n * a₀ : ℝ) : ℂ) k ^ 2 =
        reporterCoeff ((2 ^ (n + 1) * a₀ : ℝ) : ℂ) k) ∧
      (∀ x : ℤ → ℂ, reporter ((2 ^ n * a₀ : ℝ) : ℂ) (tiltSeq (2 ^ n * a₀) x) =
        reporter ((2 ^ (n + 1) * a₀ : ℝ) : ℂ) x) ∧
      ¬ (∃ φ : Fibre (2 ^ n * a₀) →L[ℂ] ℂ,
        ∀ k, φ (Fibre.atom k) = reporterCoeff ((2 ^ (n + 1) * a₀ : ℝ) : ℂ) k) ∧
      (∃ φ : Fibre (2 ^ (n + 1) * a₀) →L[ℂ] ℂ,
        ∀ k, φ (Fibre.atom k) = reporterCoeff ((2 ^ (n + 1) * a₀ : ℝ) : ℂ) k) ∧
      (∃ h : 2 ^ n * a₀ + |2 ^ n * a₀| ≤ 2 ^ (n + 1) * a₀,
        ‖Fibre.tilt (2 ^ n * a₀) h‖ = 1) := by
  haveI : Fact (0 ≤ 2 ^ n * a₀) := ⟨by positivity⟩
  haveI : Fact (0 ≤ 2 ^ (n + 1) * a₀) := ⟨by positivity⟩
  have hpow : (2 : ℝ) ^ (n + 1) * a₀ = 2 * (2 ^ n * a₀) := by ring
  have hpos : (0 : ℝ) < 2 ^ n * a₀ := by positivity
  refine ⟨fun k => ?_, fun x => ?_, ?_, ?_, ⟨?_, Fibre.norm_tilt _ _⟩⟩
  · rw [hpow]; exact (selfCatalytic _ k 0).1
  · rw [hpow]; exact (selfCatalytic _ 0 x).2
  · rw [Fibre.exists_reporter_clm_iff]
    simp only [Complex.ofReal_re]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n + 1) * a₀)]
    nlinarith
  · exact (Fibre.exists_reporter_clm_iff _).mpr (by
      rw [Complex.ofReal_re, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n + 1) * a₀)])
  · rw [abs_of_pos hpos, hpow]; linarith

/-! ## Open lineage -/

theorem tiltSeq_tiltSeq (c d : ℝ) (x : ℤ → ℂ) : tiltSeq c (tiltSeq d x) = tiltSeq (c + d) x := by
  funext k
  simp only [tiltSeq]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3; ring

/-- `n` repeated interventions `T_c` are the single intervention `T_{nc}`. -/
theorem tiltSeq_iterate (c : ℝ) (n : ℕ) (x : ℤ → ℂ) :
    (tiltSeq c)^[n] x = tiltSeq (n * c) x := by
  induction n with
  | zero => funext k; simp [tiltSeq]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, tiltSeq_tiltSeq]
    congr 1; push_cast; ring

/-- **Corollary 6.1** The least repair grade for `n` positive interventions is exactly `nc`: the
iterate is bounded `𝒜_{a+nc} → 𝒜_a` and unbounded from `𝒜_{a+β}` for every `β < nc`. -/
theorem iterate_repair_grade {c : ℝ} (hc : 0 < c) (a : ℝ) (n : ℕ) :
    (∀ x : ℤ → ℂ, Admissible (a + n * c) x → Admissible a ((tiltSeq c)^[n] x)) ∧
      ∀ β < n * c, ¬ ∃ C : ℝ, ∀ k : ℤ,
        wnorm a ((tiltSeq c)^[n] (atomSeq k)) ≤ C * wnorm (a + β) (atomSeq k) := by
  refine ⟨fun x hx => ?_, fun β hβ => ?_⟩
  · rw [tiltSeq_iterate]
    exact admissible_tiltSeq (by rw [abs_of_nonneg (by positivity)]) hx
  · simp_rw [tiltSeq_iterate]
    exact tiltSeq_loss_sharp a (by rwa [abs_of_nonneg (by positivity)])

/-- The minimal repair grade `nc` diverges. -/
theorem tendsto_repair_grade {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * c) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_const hc

/-! ## Clock multiplication -/

/-- Clock multiplication `(M x)_k = k x_k`. -/
def clockSeq (x : ℤ → ℂ) : ℤ → ℂ := fun k => (k : ℂ) * x k

theorem abs_mul_expWeight_le {a ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    |(k : ℝ)| * expWeight a k ≤ ε⁻¹ * expWeight (a + ε) k := by
  have h := Real.add_one_le_exp (ε * |(k : ℝ)|)
  have h' : |(k : ℝ)| ≤ ε⁻¹ * Real.exp (ε * |(k : ℝ)|) := by
    rw [le_inv_mul_iff₀ hε]; nlinarith [abs_nonneg (k : ℝ)]
  calc |(k : ℝ)| * expWeight a k ≤ ε⁻¹ * Real.exp (ε * |(k : ℝ)|) * expWeight a k :=
        mul_le_mul_of_nonneg_right h' (expWeight_pos a k).le
    _ = ε⁻¹ * expWeight (a + ε) k := by
        rw [expWeight, expWeight, mul_assoc, ← Real.exp_add]; congr 2; ring

theorem norm_clockSeq (x : ℤ → ℂ) (k : ℤ) : ‖clockSeq x k‖ = |(k : ℝ)| * ‖x k‖ := by
  rw [clockSeq, norm_mul, Complex.norm_intCast]

/-- **(BER.18)** Clock multiplication loses an arbitrarily small collar: `𝒜_{a+ε} → 𝒜_a`. -/
theorem admissible_clockSeq {a ε : ℝ} (hε : 0 < ε) {x : ℤ → ℂ} (hx : Admissible (a + ε) x) :
    Admissible a (clockSeq x) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _))
    (fun k => by
      rw [norm_clockSeq]
      calc expWeight a k * (|(k : ℝ)| * ‖x k‖) = |(k : ℝ)| * expWeight a k * ‖x k‖ := by ring
        _ ≤ ε⁻¹ * expWeight (a + ε) k * ‖x k‖ :=
            mul_le_mul_of_nonneg_right (abs_mul_expWeight_le hε k) (norm_nonneg _)
        _ = ε⁻¹ * (expWeight (a + ε) k * ‖x k‖) := by ring)
    (hx.mul_left ε⁻¹)

theorem wnorm_clockSeq_le {a ε : ℝ} (hε : 0 < ε) {x : ℤ → ℂ} (hx : Admissible (a + ε) x) :
    wnorm a (clockSeq x) ≤ ε⁻¹ * wnorm (a + ε) x := by
  rw [wnorm, wnorm, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (admissible_clockSeq hε hx) (hx.mul_left ε⁻¹)
  rw [norm_clockSeq]
  calc expWeight a k * (|(k : ℝ)| * ‖x k‖) = |(k : ℝ)| * expWeight a k * ‖x k‖ := by ring
    _ ≤ ε⁻¹ * expWeight (a + ε) k * ‖x k‖ :=
        mul_le_mul_of_nonneg_right (abs_mul_expWeight_le hε k) (norm_nonneg _)
    _ = ε⁻¹ * (expWeight (a + ε) k * ‖x k‖) := by ring

/-- **(BER.18)** No fixed fibre carries clock multiplication without loss. -/
theorem clockSeq_unbounded (a : ℝ) :
    ¬ ∃ C : ℝ, ∀ k : ℤ, wnorm a (clockSeq (atomSeq k)) ≤ C * wnorm a (atomSeq k) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h := hC n
  have hval : wnorm a (clockSeq (atomSeq (n : ℤ))) = n * expWeight a n := by
    rw [wnorm, tsum_eq_single (n : ℤ)]
    · rw [norm_clockSeq]; simp [atomSeq]; ring
    · intro j hj; simp [clockSeq, atomSeq, hj]
  rw [hval, wnorm_atomSeq] at h
  have := le_of_mul_le_mul_right h (expWeight_pos a n)
  linarith

/-! ## The projective receiver `𝒜_∞` -/

instance natFact (n : ℕ) : Fact (0 ≤ (n : ℝ)) := ⟨Nat.cast_nonneg n⟩

theorem Fibre.seq_algebraMap {a : ℝ} [Fact (0 ≤ a)] (c : ℂ) :
    (algebraMap ℂ (Fibre a) c).seq = c • unitSeq := by
  rw [Algebra.algebraMap_eq_smul_one, Fibre.seq_smul, Fibre.seq_one]

/-- Compatible families across all integer grades: the projective receiver `𝒜_∞`. -/
def receiverSubalgebra : Subalgebra ℂ (∀ n : ℕ, Fibre (n : ℝ)) where
  carrier := {f | ∀ m n, (f m).seq = (f n).seq}
  mul_mem' {f g} hf hg m n := by
    change (f m * g m).seq = (f n * g n).seq
    rw [Fibre.seq_mul, Fibre.seq_mul, hf m n, hg m n]
  one_mem' m n := by simp only [Pi.one_apply, Fibre.seq_one]
  add_mem' {f g} hf hg m n := by
    change (f m + g m).seq = (f n + g n).seq
    rw [Fibre.seq_add, Fibre.seq_add, hf m n, hg m n]
  zero_mem' m n := by simp only [Pi.zero_apply, Fibre.seq_zero]
  algebraMap_mem' c m n := by
    simp only [Pi.algebraMap_apply, Fibre.seq_algebraMap]

/-- The projective receiver `𝒜_∞`. -/
abbrev Receiver : Type := ↥receiverSubalgebra

namespace Receiver

/-- The common underlying sequence of a compatible family. -/
def seq (f : Receiver) : ℤ → ℂ := (f.1 0).seq

theorem seq_eq (f : Receiver) (n : ℕ) : (f.1 n).seq = f.seq := f.2 n 0

theorem admissible (f : Receiver) (a : ℝ) : Admissible a f.seq := by
  obtain ⟨n, hn⟩ := exists_nat_ge a
  have h := (f.1 n).admissible
  rw [seq_eq] at h
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (expWeight_pos a k).le (norm_nonneg _))
    (fun k => mul_le_mul_of_nonneg_right (expWeight_mono hn k) (norm_nonneg _)) h

theorem seq_injective : Function.Injective seq := fun f g h => by
  refine Subtype.ext (funext fun n => Fibre.ext ?_)
  rw [seq_eq, seq_eq, h]

/-- **(BER.16)** The receiver is exactly `⋂_{a ≥ 0} 𝒜_a`. -/
theorem range_seq (x : ℤ → ℂ) :
    x ∈ Set.range seq ↔ ∀ a : ℝ, 0 ≤ a → Admissible a x := by
  constructor
  · rintro ⟨f, rfl⟩ a _; exact f.admissible a
  · intro hx
    refine ⟨⟨fun n => Fibre.mk x (hx n (Nat.cast_nonneg n)), fun m n => ?_⟩, ?_⟩
    · simp only [Fibre.seq_mk]
    · simp only [seq, Fibre.seq_mk]

theorem isClosed_receiver : IsClosed (receiverSubalgebra : Set (∀ n : ℕ, Fibre (n : ℝ))) := by
  have hset : (receiverSubalgebra : Set (∀ n : ℕ, Fibre (n : ℝ))) =
      ⋂ (m : ℕ) (n : ℕ) (k : ℤ), {f | Fibre.coord k (f m) = Fibre.coord k (f n)} := by
    ext f
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Fibre.coord_apply]
    exact ⟨fun h m n k => congrFun (h m n) k, fun h m n => funext (h m n)⟩
  rw [hset]
  refine isClosed_iInter fun m => isClosed_iInter fun n => isClosed_iInter fun k => ?_
  exact isClosed_eq ((Fibre.coord k).continuous.comp (continuous_apply m))
    ((Fibre.coord k).continuous.comp (continuous_apply n))

instance : IsClosed (receiverSubalgebra : Set (∀ n : ℕ, Fibre (n : ℝ))) := isClosed_receiver

/-- **Theorem 5.1** `𝒜_∞` is complete. -/
instance : CompleteSpace Receiver := IsClosed.completeSpace_coe

/-- **Theorem 5.1** Formation (multiplication) is jointly continuous on `𝒜_∞`. -/
theorem continuous_mul : Continuous fun p : Receiver × Receiver => p.1 * p.2 := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

/-- **Theorem 5.1** `𝒜_∞` is locally convex. -/
theorem locallyConvexSpace : LocallyConvexSpace ℝ Receiver :=
  LocallyConvexSpace.induced
    ((receiverSubalgebra.val.toLinearMap).restrictScalars ℝ)

/-- Reflection on `𝒜_∞`. -/
def reflect : Receiver →L[ℂ] Receiver where
  toFun f := ⟨fun n => Fibre.reflect (f.1 n), fun m n => by
    change reflectSeq (f.1 m).seq = reflectSeq (f.1 n).seq
    rw [f.2 m n]⟩
  map_add' f g := Subtype.ext (funext fun n => map_add Fibre.reflect _ _)
  map_smul' c f := Subtype.ext (funext fun n => map_smul Fibre.reflect _ _)
  cont := by
    refine Continuous.subtype_mk (continuous_pi fun n => ?_) _
    exact Fibre.reflect.continuous.comp ((continuous_apply n).comp continuous_subtype_val)

/-- Phase on `𝒜_∞`. -/
def phase (t : ℝ) : Receiver →L[ℂ] Receiver where
  toFun f := ⟨fun n => Fibre.phase t (f.1 n), fun m n => by
    change phaseSeq t (f.1 m).seq = phaseSeq t (f.1 n).seq
    rw [f.2 m n]⟩
  map_add' f g := Subtype.ext (funext fun n => map_add (Fibre.phase t) _ _)
  map_smul' c f := Subtype.ext (funext fun n => map_smul (Fibre.phase t) _ _)
  cont := by
    refine Continuous.subtype_mk (continuous_pi fun n => ?_) _
    exact (Fibre.phase t).continuous.comp ((continuous_apply n).comp continuous_subtype_val)

theorem grade_bound (c : ℝ) (n : ℕ) : (n : ℝ) + |c| ≤ ((n + ⌈|c|⌉₊ : ℕ) : ℝ) := by
  push_cast; linarith [Nat.le_ceil |c|]

/-- **Theorem 5.1** Every horizontal intervention acts continuously on `𝒜_∞`. -/
def tilt (c : ℝ) : Receiver →L[ℂ] Receiver where
  toFun f := ⟨fun n => Fibre.tilt c (grade_bound c n) (f.1 (n + ⌈|c|⌉₊)), fun m n => by
    change tiltSeq c (f.1 (m + ⌈|c|⌉₊)).seq = tiltSeq c (f.1 (n + ⌈|c|⌉₊)).seq
    rw [f.2 (m + ⌈|c|⌉₊) (n + ⌈|c|⌉₊)]⟩
  map_add' f g := Subtype.ext (funext fun n => map_add (Fibre.tilt c _) _ _)
  map_smul' r f := Subtype.ext (funext fun n => map_smul (Fibre.tilt c _) _ _)
  cont := by
    refine Continuous.subtype_mk (continuous_pi fun n => ?_) _
    exact (Fibre.tilt c _).continuous.comp
      ((continuous_apply (n + ⌈|c|⌉₊)).comp continuous_subtype_val)

theorem seq_reflect (f : Receiver) : (reflect f).seq = reflectSeq f.seq := rfl
theorem seq_phase (t : ℝ) (f : Receiver) : (phase t f).seq = phaseSeq t f.seq := rfl
theorem seq_tilt (c : ℝ) (f : Receiver) : (tilt c f).seq = tiltSeq c f.seq := by
  change tiltSeq c (f.1 (0 + ⌈|c|⌉₊)).seq = tiltSeq c f.seq
  rw [seq_eq]

/-- Phase stays periodic on `𝒜_∞`. -/
theorem phase_add_two_pi (t : ℝ) (f : Receiver) : phase (t + 2 * Real.pi) f = phase t f :=
  seq_injective (phaseSeq_add_two_pi t f.seq)

theorem reporter_bound (z : ℂ) : |z.re| ≤ ((⌈|z.re|⌉₊ : ℕ) : ℝ) := Nat.le_ceil _

/-- **Theorem 5.1** Every exponential reporter is a continuous character of `𝒜_∞`. -/
def reporterHom (z : ℂ) : Receiver →ₐ[ℂ] ℂ :=
  (Fibre.reporterHom z (reporter_bound z)).comp
    ((Pi.evalAlgHom ℂ (fun n : ℕ => Fibre (n : ℝ)) ⌈|z.re|⌉₊).comp receiverSubalgebra.val)

theorem reporterHom_apply (z : ℂ) (f : Receiver) : reporterHom z f = reporter z f.seq := by
  change reporter z (f.1 ⌈|z.re|⌉₊).seq = reporter z f.seq
  rw [seq_eq]

theorem continuous_reporterHom (z : ℂ) : Continuous (reporterHom z) :=
  (Fibre.reporterCLM z (reporter_bound z)).continuous.comp
    ((continuous_apply ⌈|z.re|⌉₊).comp continuous_subtype_val)

/-- Clock multiplication `𝒜_{a+1} → 𝒜_a` on a fibre. -/
def Fibre.clock (n : ℕ) : Fibre ((n + 1 : ℕ) : ℝ) →L[ℂ] Fibre (n : ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun x => Fibre.mk (clockSeq x.seq)
        (admissible_clockSeq (a := n) one_pos (by
          have := x.admissible; push_cast at this; exact this))
      map_add' := fun x y => Fibre.ext (funext fun k => by simp [clockSeq, mul_add])
      map_smul' := fun r x => Fibre.ext (funext fun k => by simp [clockSeq]; ring) } 1
    fun x => by
      have h := wnorm_clockSeq_le (a := n) one_pos (x := x.seq)
        (by have := x.admissible; push_cast at this; exact this)
      rw [inv_one, one_mul] at h
      rw [one_mul]
      change wnorm n (clockSeq x.seq) ≤ wnorm ((n + 1 : ℕ) : ℝ) x.seq
      push_cast
      exact h

/-- **(BER.18)** Clock multiplication acts continuously on `𝒜_∞`. -/
def clock : Receiver →L[ℂ] Receiver where
  toFun f := ⟨fun n => Fibre.clock n (f.1 (n + 1)), fun m n => by
    change clockSeq (f.1 (m + 1)).seq = clockSeq (f.1 (n + 1)).seq
    rw [f.2 (m + 1) (n + 1)]⟩
  map_add' f g := Subtype.ext (funext fun n => map_add (Fibre.clock n) _ _)
  map_smul' r f := Subtype.ext (funext fun n => map_smul (Fibre.clock n) _ _)
  cont := by
    refine Continuous.subtype_mk (continuous_pi fun n => ?_) _
    exact (Fibre.clock n).continuous.comp ((continuous_apply (n + 1)).comp continuous_subtype_val)

theorem seq_clock (f : Receiver) : (clock f).seq = clockSeq f.seq := by
  change clockSeq (f.1 (0 + 1)).seq = clockSeq f.seq
  rw [seq_eq]

/-- **(BER.18)** Every finite clock jet `M^j` acts continuously on `𝒜_∞`, by `k^j x_k`. -/
theorem seq_clock_pow (j : ℕ) (f : Receiver) :
    ((clock ^ j) f).seq = fun k : ℤ => (k : ℂ) ^ j * f.seq k := by
  induction j generalizing f with
  | zero => funext k; simp
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp, seq_clock, ih]
    funext k; simp only [clockSeq]; ring

end Receiver

end

end GaloisForLFunctions.HTGeometry.BilateralRepair
