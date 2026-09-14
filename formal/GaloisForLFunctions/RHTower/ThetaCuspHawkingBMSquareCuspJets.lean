import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularGlobalGrowth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalCutoffLaplacian
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceOverlap
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularLaplacian
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCoreTestData
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceAngularAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMWeightedSquareCuspBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularScalarEquation

/-! Every actual coordinate jet of the full squared-source cusp remainder has
all complex height-weighted bounds and global exponential log-height bounds. The proof differentiates the complete
signed Fourier–Bessel family and retains both principal–tail cross terms.
The quartic contact fields have the same derivative bounds, actual regulated
L²/L¹ admission, and an integrated principal-subtracted cusp Green-flux limit.
Constructed modular core cutoffs transpose against the actual physical QNM
angular test, retaining both height-derivative cutoff terms. -/

open Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMSquareCuspJets
open D4BMAngularSeries D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

private abbrev Field := (Fin 2 → ℝ) → ℂ

/-- A word of actual horizontal/height Fréchet coordinate derivatives. -/
def coordinateJet : List (Fin 2) → Field → Field
  | [], f => f
  | i :: word, f => coordDeriv i (coordinateJet word f)

private inductive Rapid : Field → Prop
  | zero : Rapid (fun _ => 0)
  | bessel (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool) :
      Rapid (value u nu a d negative)
  | add {f g : Field} : Rapid f → Rapid g → Rapid (fun z => f z + g z)
  | scale (c : ℂ) {f : Field} : Rapid f → Rapid (fun z => c * f z)
  | power (w : ℂ) {f : Field} : Rapid f → Rapid (fun z => (z 1 : ℂ)^w * f z)
  | mul {f g : Field} : Rapid f → Rapid g → Rapid (fun z => f z * g z)
  | congr {f g : Field} : Rapid f → (∀ z, 0 < z 1 → f z = g z) → Rapid g

private theorem Rapid.smooth {f : Field} (h : Rapid f) : ContDiffOn ℝ ∞ f domain := by
  induction h with
  | zero => exact contDiffOn_const
  | bessel u nu a d negative => exact value_contDiffOn u nu a d negative
  | add _ _ hf hg => exact hf.add hg
  | scale c _ hf => exact contDiffOn_const.mul hf
  | power w _ hf => exact (height_cpow_contDiffOn w ∞).mul hf
  | mul _ _ hf hg => exact hf.mul hg
  | congr _ he hf => exact hf.congr (fun z hz => (he z hz).symm)

private theorem Rapid.differentiable {f : Field} (h : Rapid f)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) : DifferentiableAt ℝ f z :=
  (h.smooth.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).differentiableAt
    (by simp)

private theorem Rapid.bound {f : Field} (h : Rapid f) (w : ℂ)
    (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 → ‖(z 1:ℂ)^w * f z‖ ≤ C := by
  induction h generalizing w with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | bessel u nu a d negative => exact weighted_value_bounded u nu w a d negative l hl
  | add hf hg ihf ihg =>
      obtain ⟨A,hA,ha⟩ := ihf w
      obtain ⟨B,hB,hb⟩ := ihg w
      refine ⟨A+B,add_nonneg hA hB,?_⟩
      intro z hz
      rw [mul_add]
      exact (norm_add_le _ _).trans (add_le_add (ha z hz) (hb z hz))
  | scale c hf ih =>
      obtain ⟨A,hA,ha⟩ := ih w
      refine ⟨‖c‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
      intro z hz
      rw [mul_left_comm, norm_mul]
      exact mul_le_mul_of_nonneg_left (ha z hz) (norm_nonneg _)
  | power v hf ih =>
      obtain ⟨A,hA,ha⟩ := ih (w+v)
      refine ⟨A,hA,?_⟩
      intro z hz
      rw [← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hl.trans_le hz).ne')]
      exact ha z hz
  | mul hf hg ihf ihg =>
      obtain ⟨A,hA,ha⟩ := ihf w
      obtain ⟨B,hB,hb⟩ := ihg 0
      refine ⟨A*B,mul_nonneg hA hB,?_⟩
      intro z hz
      have hg : ‖_‖ ≤ B := hb z hz
      simp only [Complex.cpow_zero,one_mul] at hg
      rw [← mul_assoc, norm_mul]
      exact mul_le_mul (ha z hz) hg (norm_nonneg _) hA
  | congr hf he ih =>
      obtain ⟨A,hA,ha⟩ := ih w
      exact ⟨A,hA,fun z hz => by rw [← he z (hl.trans_le hz)]; exact ha z hz⟩

private theorem Rapid.global_log_growth {f : Field} (h : Rapid f) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x k : ℝ,
      ‖f ![x,Real.exp k]‖ ≤ C * Real.exp (B * |k|) := by
  induction h with
  | zero => exact ⟨0,0,le_rfl,le_rfl,by simp⟩
  | bessel u nu a d negative => exact value_global_log_growth u nu a d negative
  | add hf hg ihf ihg =>
      obtain ⟨C,B,hC,hB,hf⟩ := ihf
      obtain ⟨D,A,hD,hA,hg⟩ := ihg
      refine ⟨C+D,B+A,add_nonneg hC hD,add_nonneg hB hA,?_⟩
      intro x k
      calc
        _ ≤ C * Real.exp (B * |k|) + D * Real.exp (A * |k|) :=
          (norm_add_le _ _).trans (add_le_add (hf x k) (hg x k))
        _ ≤ C * Real.exp ((B+A) * |k|) + D * Real.exp ((B+A) * |k|) := by gcongr <;> linarith
        _ = _ := by ring
  | scale c hf ih =>
      obtain ⟨C,B,hC,hB,hf⟩ := ih
      refine ⟨‖c‖*C,B,mul_nonneg (norm_nonneg _) hC,hB,?_⟩
      intro x k
      rw [norm_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left (hf x k) (norm_nonneg _)
  | power w hf ih =>
      obtain ⟨C,B,hC,hB,hf⟩ := ih
      refine ⟨C,|w.re|+B,hC,add_nonneg (abs_nonneg _) hB,?_⟩
      intro x k
      have hp : ‖(Real.exp k:ℂ)^w‖ ≤ Real.exp (|w.re| * |k|) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos k),← Real.exp_mul]
        apply Real.exp_le_exp.mpr
        simpa only [abs_mul,mul_comm] using le_abs_self (k*w.re)
      simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
      calc
        _ = ‖(Real.exp k:ℂ)^w‖ * ‖_‖ := norm_mul _ _
        _ ≤ Real.exp (|w.re| * |k|) * (C * Real.exp (B * |k|)) :=
          mul_le_mul hp (hf x k) (norm_nonneg _) (Real.exp_nonneg _)
        _ = _ := by rw [mul_left_comm,← Real.exp_add]; congr 2; ring
  | mul hf hg ihf ihg =>
      obtain ⟨C,B,hC,hB,hf⟩ := ihf
      obtain ⟨D,A,hD,hA,hg⟩ := ihg
      refine ⟨C*D,B+A,mul_nonneg hC hD,add_nonneg hB hA,?_⟩
      intro x k
      calc
        _ = ‖_‖*‖_‖ := norm_mul _ _
        _ ≤ (C * Real.exp (B * |k|)) * (D * Real.exp (A * |k|)) :=
          mul_le_mul (hf x k) (hg x k) (norm_nonneg _) (by positivity)
        _ = _ := by rw [mul_mul_mul_comm,← Real.exp_add]; congr 2; ring
  | congr hf he ih =>
      obtain ⟨C,B,hC,hB,hf⟩ := ih
      exact ⟨C,B,hC,hB,fun x k => by rw [← he _ (Real.exp_pos k)]; exact hf x k⟩
private theorem Rapid.derivative {f : Field} (h : Rapid f) (i : Fin 2) :
    Rapid (coordDeriv i f) := by
  induction h with
  | zero =>
      apply Rapid.zero.congr
      intro z hz
      simp [coordDeriv]
  | bessel u nu a d negative =>
      fin_cases i
      · apply (Rapid.scale (horizontalRate negative) (Rapid.bessel u nu a (d+1) negative)).congr
        intro z hz
        simp [coordDeriv,(value_hasFDerivAt u nu a d negative z hz).fderiv,valueGradient,D4BMAngularSeries.gradient]
      · apply (Rapid.add (Rapid.scale (a:ℂ) (Rapid.bessel u nu (a-1) d negative))
          (Rapid.scale (-(Real.pi:ℂ)) (Rapid.add
            (Rapid.bessel u (nu+1) a (d+1) negative)
            (Rapid.bessel u (nu-1) a (d+1) negative)))).congr
        intro z hz
        simp [coordDeriv,(value_hasFDerivAt u nu a d negative z hz).fderiv,valueGradient,D4BMAngularSeries.gradient]
        ring
  | @add f g hf hg ihf ihg =>
      apply (Rapid.add ihf ihg).congr
      intro z hz
      simp [coordDeriv,fderiv_fun_add (hf.differentiable z hz) (hg.differentiable z hz)]
  | @scale c f hf ih =>
      apply (Rapid.scale c ih).congr
      intro z hz
      unfold coordDeriv
      rw [((hf.differentiable z hz).hasFDerivAt.const_mul c).fderiv]
      simp
  | @power w f hf ih =>
      apply (Rapid.add (Rapid.scale (if i=1 then w else 0) (Rapid.power (w-1) hf))
        (Rapid.power w ih)).congr
      intro z hz
      unfold coordDeriv
      rw [fderiv_fun_mul (height_cpow_hasFDerivAt w z hz).differentiableAt
        (hf.differentiable z hz), (height_cpow_hasFDerivAt w z hz).fderiv]
      fin_cases i
      · simp [D4BMAngularSeries.gradient]
      · simp [D4BMAngularSeries.gradient]
        ring
  | @mul f g hf hg ihf ihg =>
      apply (Rapid.add (Rapid.mul ihf hg) (Rapid.mul hf ihg)).congr
      intro z hz
      unfold coordDeriv
      rw [fderiv_fun_mul (hf.differentiable z hz) (hg.differentiable z hz)]
      simp
      ring
  | @congr f g hf he ih =>
      apply ih.congr
      intro z hz
      have he' : f =ᶠ[𝓝 z] g := by
        filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with v hv
        exact he v hv
      exact congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℂ => L (Pi.single i 1)) he'.fderiv_eq

private theorem Rapid.jet {f : Field} (h : Rapid f) (word : List (Fin 2)) :
    Rapid (coordinateJet word f) := by
  induction word with
  | nil => exact h
  | cons i word ih => exact ih.derivative i

private theorem tail_rapid (u : ℂ) : Rapid (tail u) := by
  apply (Rapid.scale 2 (Rapid.add (Rapid.bessel u u (1/2) 0 false)
    (Rapid.bessel u u (1/2) 0 true))).congr
  intro z hz
  simp only [tail,d4BMCompletedEisensteinCuspTailPart,d4BMCompletedEisensteinFullSignedZeroWord,
    signedTail_eq_value _ _ _ _ _ z hz,Nat.cast_zero,zero_add]

private theorem principal_mul_rapid (u : ℂ) {f : Field} (hf : Rapid f) :
    Rapid (fun z => principal u z * f z) := by
  apply (Rapid.add
    (Rapid.scale (d4BMCompletedEisensteinCuspConstantCoefficient u false)
      (Rapid.power (d4BMCompletedEisensteinCuspWeylExponent u false) hf))
    (Rapid.scale (d4BMCompletedEisensteinCuspConstantCoefficient u true)
      (Rapid.power (d4BMCompletedEisensteinCuspWeylExponent u true) hf))).congr
  intro z hz
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,mul_one]
  ring

private theorem squareRemainder_rapid (u : ℂ) : Rapid (squareRemainder u) := by
  apply (Rapid.add (Rapid.scale 2 (principal_mul_rapid u (tail_rapid u)))
    (Rapid.mul (tail_rapid u) (tail_rapid u))).congr
  intro z hz
  rw [squareRemainder_eq]
  ring

private theorem Rapid.laplacian {f : Field} (h : Rapid f) :
    Rapid (hyperbolicLaplacian f) := by
  apply (Rapid.power 2 (Rapid.add ((h.derivative 0).derivative 0)
    ((h.derivative 1).derivative 1))).congr
  intro z hz
  simp only [Complex.cpow_ofNat,hyperbolicLaplacian]

/-- The retained fourth-order angular operator on the complete square remainder. -/
def spinTwoRemainder (u : ℂ) : Field := fun z =>
  -hyperbolicLaplacian (hyperbolicLaplacian (squareRemainder u)) z +
    2*hyperbolicLaplacian (squareRemainder u) z

private theorem spinTwoRemainder_rapid (u : ℂ) : Rapid (spinTwoRemainder u) := by
  apply (Rapid.add (Rapid.scale (-1) (squareRemainder_rapid u).laplacian.laplacian)
    (Rapid.scale 2 (squareRemainder_rapid u).laplacian)).congr
  intro z hz
  simp [spinTwoRemainder]

private theorem Rapid.vanish {f : Field} (h : Rapid f) (w : ℂ) (X : ℝ → ℝ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w * f ![X y,y]) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := h.bound (w+1) 1 (by norm_num)
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [eventually_ge_atTop (max 1 (C/epsilon+1))] with y hy
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy1
  have hCy : C/y < epsilon := by
    apply (div_lt_iff₀ hy0).mpr
    have ht : C/epsilon+1 ≤ y := (le_max_right _ _).trans hy
    have he : C/epsilon*epsilon=C := div_mul_cancel₀ C hepsilon.ne'
    nlinarith
  have heq : (y:ℂ)^w * f ![X y,y] =
      ((y:ℂ)^(w+1) * f ![X y,y]) / (y:ℂ) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy0.ne'),Complex.cpow_one]
    field_simp [Complex.ofReal_ne_zero.mpr hy0.ne']
  rw [dist_zero_right,heq,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy0]
  exact (div_le_div_of_nonneg_right (hb ![X y,y] hy1) hy0.le).trans_lt hCy

/-- Every genuine remainder jet has a uniform exponential bound in absolute log-height. -/
theorem squareRemainder_jet_global_log_growth (u : ℂ) (word : List (Fin 2)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x k : ℝ,
      ‖coordinateJet word (squareRemainder u) ![x,Real.exp k]‖ ≤ C * Real.exp (B * |k|) :=
  ((squareRemainder_rapid u).jet word).global_log_growth

/-- Every genuine coordinate jet of the complete squared-source remainder is
bounded after any complex height weight, uniformly over the whole half-strip. -/
theorem squareRemainder_jet_weighted_bound (u w : ℂ) (word : List (Fin 2)) (l : Ioi (0:ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l.val ≤ z 1 →
      ‖(z 1:ℂ)^w * coordinateJet word (squareRemainder u) z‖ ≤ C :=
  ((squareRemainder_rapid u).jet word).bound w l.val l.property

/-- Every genuine remainder jet has a uniform exponential bound in absolute log-height. -/
theorem spinTwoRemainder_jet_global_log_growth (u : ℂ) (word : List (Fin 2)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x k : ℝ,
      ‖coordinateJet word (spinTwoRemainder u) ![x,Real.exp k]‖ ≤ C * Real.exp (B * |k|) :=
  ((spinTwoRemainder_rapid u).jet word).global_log_growth

/-- The original fourth-order angular remainder and every further coordinate
jet have all height-weighted bounds; no angular operator is discarded. -/
theorem spinTwoRemainder_jet_weighted_bound (u w : ℂ) (word : List (Fin 2)) (l : Ioi (0:ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l.val ≤ z 1 →
      ‖(z 1:ℂ)^w * coordinateJet word (spinTwoRemainder u) z‖ ≤ C :=
  ((spinTwoRemainder_rapid u).jet word).bound w l.val l.property

/-- Every weighted source-remainder jet vanishes along any horizontal path to
infinite cusp height, without a regularity restriction on that path. -/
theorem squareRemainder_jet_tendsto_zero (u w : ℂ) (word : List (Fin 2)) (X : ℝ → ℝ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w * coordinateJet word (squareRemainder u) ![X y,y])
      atTop (𝓝 0) :=
  ((squareRemainder_rapid u).jet word).vanish w X

/-- The complete retained spin-two remainder obeys the same arbitrary-path
cusp limit after every further derivative and complex height weight. -/
theorem spinTwoRemainder_jet_tendsto_zero (u w : ℂ) (word : List (Fin 2)) (X : ℝ → ℝ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w * coordinateJet word (spinTwoRemainder u) ![X y,y])
      atTop (𝓝 0) :=
  ((spinTwoRemainder_rapid u).jet word).vanish w X

/-- Every actual source-remainder coordinate jet is smooth on the complete
positive-height chart; no caller-supplied regularity is needed. -/
theorem squareRemainder_jet_smooth (u : ℂ) (word : List (Fin 2)) :
    ContDiffOn ℝ ∞ (coordinateJet word (squareRemainder u)) domain :=
  ((squareRemainder_rapid u).jet word).smooth


private inductive Principal : Field → Prop
  | power (w : ℂ) : Principal (fun z => (z 1:ℂ)^w)
  | add {f g : Field} : Principal f → Principal g → Principal (fun z => f z+g z)
  | scale (c : ℂ) {f : Field} : Principal f → Principal (fun z => c*f z)
  | mul {f g : Field} : Principal f → Principal g → Principal (fun z => f z*g z)
  | congr {f g : Field} : Principal f → (∀ z, 0 < z 1 → f z=g z) → Principal g

private theorem Principal.smooth {f : Field} (h : Principal f) :
    ContDiffOn ℝ ∞ f domain := by
  induction h with
  | power w => exact height_cpow_contDiffOn w ∞
  | add _ _ hf hg => exact hf.add hg
  | scale c _ hf => exact contDiffOn_const.mul hf
  | mul _ _ hf hg => exact hf.mul hg
  | congr _ he hf => exact hf.congr (fun z hz => (he z hz).symm)

private theorem Principal.differentiable {f : Field} (h : Principal f)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) : DifferentiableAt ℝ f z :=
  (h.smooth.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).differentiableAt
    (by simp)

private theorem Principal.derivative {f : Field} (h : Principal f) (i : Fin 2) :
    Principal (coordDeriv i f) := by
  induction h with
  | power w =>
      apply (Principal.scale (if i=1 then w else 0) (Principal.power (w-1))).congr
      intro z hz
      unfold coordDeriv
      rw [(height_cpow_hasFDerivAt w z hz).fderiv]
      fin_cases i <;> simp [D4BMAngularSeries.gradient]
  | @add f g hf hg ihf ihg =>
      apply (Principal.add ihf ihg).congr
      intro z hz
      simp [coordDeriv,fderiv_fun_add (hf.differentiable z hz) (hg.differentiable z hz)]
  | @scale c f hf ih =>
      apply (Principal.scale c ih).congr
      intro z hz
      unfold coordDeriv
      rw [((hf.differentiable z hz).hasFDerivAt.const_mul c).fderiv]
      simp
  | @mul f g hf hg ihf ihg =>
      apply (Principal.add (Principal.mul ihf hg) (Principal.mul hf ihg)).congr
      intro z hz
      unfold coordDeriv
      rw [fderiv_fun_mul (hf.differentiable z hz) (hg.differentiable z hz)]
      simp
      ring
  | @congr f g hf he ih =>
      apply ih.congr
      intro z hz
      have he' : f =ᶠ[𝓝 z] g := by
        filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with v hv
        exact he v hv
      exact congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℂ => L (Pi.single i 1)) he'.fderiv_eq

private theorem Principal.laplacian {f : Field} (h : Principal f) :
    Principal (hyperbolicLaplacian f) := by
  apply (Principal.mul (Principal.power 2) (Principal.add ((h.derivative 0).derivative 0)
    ((h.derivative 1).derivative 1))).congr
  intro z hz
  simp only [Complex.cpow_ofNat,hyperbolicLaplacian]

private theorem Principal.mul_rapid {f g : Field} (hf : Principal f) (hg : Rapid g) :
    Rapid (fun z => f z*g z) := by
  induction hf generalizing g with
  | power w => exact Rapid.power w hg
  | @add f h hf hh ihf ihh =>
      apply (Rapid.add (ihf hg) (ihh hg)).congr
      intro z hz
      ring
  | scale c hf ih =>
      apply (Rapid.scale c (ih hg)).congr
      intro z hz
      ring
  | @mul f h hf hh ihf ihh =>
      have he := ihf (ihh hg)
      apply he.congr
      intro z hz
      ring
  | @congr f h hf he ih =>
      apply (ih hg).congr
      intro z hz
      rw [he z hz]

private theorem literal_principal (u : ℂ) : Principal (principal u) := by
  apply (Principal.add
    (Principal.scale (d4BMCompletedEisensteinCuspConstantCoefficient u false)
      (Principal.power (d4BMCompletedEisensteinCuspWeylExponent u false)))
    (Principal.scale (d4BMCompletedEisensteinCuspConstantCoefficient u true)
      (Principal.power (d4BMCompletedEisensteinCuspWeylExponent u true)))).congr
  intro z hz
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,mul_one]

private theorem derivative_smooth {f : Field} (hf : ContDiffOn ℝ ∞ f domain) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordDeriv i f) domain := by
  intro z hz
  exact (((hf.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt

private theorem laplacian_smooth {f : Field} (hf : ContDiffOn ℝ ∞ f domain) :
    ContDiffOn ℝ ∞ (hyperbolicLaplacian f) domain := by
  have hy := height_cpow_contDiffOn (2:ℂ) ∞
  simp only [Complex.cpow_ofNat] at hy
  exact hy.mul ((derivative_smooth (derivative_smooth hf 0) 0).add
    (derivative_smooth (derivative_smooth hf 1) 1))

private inductive AngularExpression
  | seed
  | add (f g : AngularExpression)
  | mul (f g : AngularExpression)
  | scale (c : ℂ) (f : AngularExpression)
  | lap (f : AngularExpression)

private def AngularExpression.eval (u : ℂ) (principalOnly : Bool) : AngularExpression → Field
  | .seed => if principalOnly then principal u else scalar u
  | .add f g => fun z => f.eval u principalOnly z+g.eval u principalOnly z
  | .mul f g => fun z => f.eval u principalOnly z*g.eval u principalOnly z
  | .scale c f => fun z => c*f.eval u principalOnly z
  | .lap f => hyperbolicLaplacian (f.eval u principalOnly)

private theorem AngularExpression.principal (e : AngularExpression) (u : ℂ) :
    Principal (e.eval u true) := by
  induction e with
  | seed => exact literal_principal u
  | add f g hf hg => exact Principal.add hf hg
  | mul f g hf hg => exact Principal.mul hf hg
  | scale c f hf => exact Principal.scale c hf
  | lap f hf => exact hf.laplacian

private theorem AngularExpression.smooth (e : AngularExpression) (u : ℂ) (b : Bool) :
    ContDiffOn ℝ ∞ (e.eval u b) domain := by
  induction e with
  | seed =>
      cases b
      · exact cuspLeg_contDiffOn .scalar u
      · exact (literal_principal u).smooth
  | add f g hf hg => exact hf.add hg
  | mul f g hf hg => exact hf.mul hg
  | scale c f hf => exact contDiffOn_const.mul hf
  | lap f hf => exact laplacian_smooth hf

private theorem AngularExpression.remainder (e : AngularExpression) (u : ℂ) :
    Rapid (fun z => e.eval u false z-e.eval u true z) := by
  induction e with
  | seed =>
      apply (tail_rapid u).congr
      intro z hz
      change tail u z=(D4BMGlobalAngularResponse.principal u z+tail u z)-D4BMGlobalAngularResponse.principal u z
      ring
  | add f g hf hg =>
      apply (Rapid.add hf hg).congr
      intro z hz
      simp only [AngularExpression.eval]
      ring
  | mul f g hf hg =>
      apply (Rapid.add ((f.principal u).mul_rapid hg)
        (Rapid.add ((g.principal u).mul_rapid hf) (Rapid.mul hf hg))).congr
      intro z hz
      simp only [AngularExpression.eval]
      ring
  | scale c f hf =>
      apply (Rapid.scale c hf).congr
      intro z hz
      simp only [AngularExpression.eval]
      ring
  | lap f hf =>
      apply hf.laplacian.congr
      intro z hz
      have hpos : domain ∈ 𝓝 z := (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
      have ha : ContDiffAt ℝ 2 (f.eval u false) z :=
        ((f.smooth u false).contDiffAt hpos).of_le (by norm_cast)
      have hb : ContDiffAt ℝ 2 (f.eval u true) z :=
        ((f.smooth u true).contDiffAt hpos).of_le (by norm_cast)
      have he : (fun w => f.eval u false w-f.eval u true w) =
          (fun w => f.eval u false w+(-1:ℂ)*f.eval u true w) := by funext w; ring
      rw [he,hyperbolicLaplacian_add ha (contDiffAt_const.mul hb),
        hyperbolicLaplacian_const_mul hb]
      simp only [AngularExpression.eval]
      ring

private def quarticExpression (c : ℂ) : Fin 6 → AngularExpression := fun slot =>
  let Q := AngularExpression.scale (1/2) (.mul .seed .seed)
  let J := AngularExpression.scale (1/8) (.add (.scale c Q) (.scale (-2) (.lap Q)))
  let R := AngularExpression.add (.scale (-1) (.lap (.lap Q))) (.scale 2 (.lap Q))
  let Q2 := AngularExpression.mul Q Q
  let J2 := AngularExpression.mul J J
  let H := AngularExpression.add (.scale 2 J2) (.scale (c*(c-4)/96) Q2)
  ![Q2,J2,.add (.scale (1/2) (.lap J2)) (.scale (-1) (.mul J (.lap J))),.mul J R,H,.lap H] slot

/-- Actual quartic angular fields: Q², J², the bilinear contact-gradient expression,
J[-Delta(Delta-2)Q], H=2J²+c(c-4)Q²/96, and Delta H, in that order. -/
def quarticContactField (q : XiZeroCopy) (slot : Fin 6) : Field :=
  (quarticExpression (7*((center q)^2-1/4)-2) slot).eval (center q) false

/-- Full principal expression obtained by applying the same actual products and
angular derivatives to both original Weyl powers. -/
def quarticContactPrincipal (q : XiZeroCopy) (slot : Fin 6) : Field :=
  (quarticExpression (7*((center q)^2-1/4)-2) slot).eval (center q) true

/-- The original height-two/height-three cutoff, with every principal term retained. -/
def quarticContactResidual (q : XiZeroCopy) (slot : Fin 6) (z : Fin 2 → ℝ) : ℂ :=
  quarticContactField q slot z-cutoff z*quarticContactPrincipal q slot z

/-- Every genuine derivative of all six nonlinear contact remainders has every
complex height-weighted bound, from the literal Fourier source. -/
theorem quarticContact_remainder_jet_bound (q : XiZeroCopy) (slot : Fin 6)
    (w : ℂ) (word : List (Fin 2)) (l : Ioi (0:ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l.val ≤ z 1 →
      ‖(z 1:ℂ)^w*coordinateJet word
        (fun z => quarticContactField q slot z-quarticContactPrincipal q slot z) z‖ ≤ C :=
  (((quarticExpression _ slot).remainder (center q)).jet word).bound w l.val l.property

/-- Actual weighted derivative remainders vanish along every path into the cusp. -/
theorem quarticContact_remainder_jet_tendsto_zero (q : XiZeroCopy) (slot : Fin 6)
    (w : ℂ) (word : List (Fin 2)) (X : ℝ → ℝ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*coordinateJet word
      (fun z => quarticContactField q slot z-quarticContactPrincipal q slot z) ![X y,y])
      atTop (𝓝 0) :=
  (((quarticExpression _ slot).remainder (center q)).jet word).vanish w X

private theorem quarticContact_pair_rapid (q : XiZeroCopy) (slot : Fin 6) (u : ℂ) :
    Rapid (fun z => scalar u z*(quarticContactField q slot z-quarticContactPrincipal q slot z)) := by
  have hr := (quarticExpression (7*((center q)^2-1/4)-2) slot).remainder (center q)
  apply (Rapid.add ((literal_principal u).mul_rapid hr) (Rapid.mul (tail_rapid u) hr)).congr
  intro z hz
  let r := fun z => quarticContactField q slot z-quarticContactPrincipal q slot z
  change principal u z*r z+tail u z*r z=(principal u z+tail u z)*r z
  ring

/-- All six original cutoff-subtracted contact fields pair in the actual quotient
L² space with every full scalar testing field, including every physical Xi test. -/
theorem quarticContactResidual_scalar_memLp (q : XiZeroCopy) (slot : Fin 6) (u : ℂ) :
    MeasureTheory.MemLp (fun z : UpperHalfPlane =>
      scalar u (coordinates z)*quarticContactResidual q slot (coordinates z))
      2 D4BMModularCore.measure := by
  obtain ⟨C,-,hC⟩ := (quarticContact_pair_rapid q slot u).bound 0 3 (by norm_num)
  have hf := ((quarticExpression (7*((center q)^2-1/4)-2) slot).smooth (center q) false).continuousOn
  have hp := ((quarticExpression (7*((center q)^2-1/4)-2) slot).smooth (center q) true).continuousOn
  have hc : ContinuousOn (quarticContactResidual q slot) domain :=
    hf.sub (D4BMJointSource.sourceCutoff_smooth.continuous.continuousOn.mul hp)
  apply D4BMJointSource.cuspBound_memLp _ ((cuspLeg_contDiffOn .scalar u).continuousOn.mul hc) C
  intro z hz
  have he : cutoff z=1 := by
    unfold cutoff
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  change ‖scalar u z*quarticContactResidual q slot z‖ ≤ C
  simpa only [quarticContactResidual,he,one_mul,Complex.cpow_zero] using hC z hz.le

/-- Absolute admission of the complete quartic contact periods before their
explicit native Mellin corrections; no regularity or integrability premise is supplied. -/
theorem quarticContactResidual_scalar_integrable (q : XiZeroCopy) (slot : Fin 6) (u : ℂ) :
    MeasureTheory.Integrable (fun z : UpperHalfPlane =>
      scalar u (coordinates z)*quarticContactResidual q slot (coordinates z)) D4BMModularCore.measure :=
  MeasureTheory.MemLp.integrable (by norm_num) (quarticContactResidual_scalar_memLp q slot u)

private theorem AngularExpression.derivative_remainder (e : AngularExpression) (u : ℂ) (i : Fin 2) :
    Rapid (fun z => coordDeriv i (e.eval u false) z-coordDeriv i (e.eval u true) z) := by
  apply ((e.remainder u).derivative i).congr
  intro z hz
  have hn : domain ∈ 𝓝 z := (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have hf := ((e.smooth u false).contDiffAt hn).differentiableAt (by simp)
  have hp := ((e.smooth u true).contDiffAt hn).differentiableAt (by simp)
  unfold coordDeriv
  exact congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℂ => L (Pi.single i 1))
    (hf.hasFDerivAt.sub hp.hasFDerivAt).fderiv

private theorem product_remainder_rapid {f f0 g g0 : Field}
    (hf : Rapid (fun z => f z-f0 z)) (hp : Principal f0)
    (hg : Rapid (fun z => g z-g0 z)) (hq : Principal g0) :
    Rapid (fun z => f z*g z-f0 z*g0 z) := by
  apply (Rapid.add (hp.mul_rapid hg) (Rapid.add (hq.mul_rapid hf) (Rapid.mul hf hg))).congr
  intro z hz
  ring

/-- The complete gradient product after subtracting both principal derivatives. -/
def gradientProductRemainder (u : ℂ) (i j : Fin 2) : Field := fun z =>
  coordDeriv i (scalar u) z*coordDeriv j (scalar u) z-
    coordDeriv i (principal u) z*coordDeriv j (principal u) z

private theorem gradientProductRemainder_rapid (u : ℂ) (i j : Fin 2) :
    Rapid (gradientProductRemainder u i j) :=
  product_remainder_rapid (AngularExpression.seed.derivative_remainder u i)
    ((literal_principal u).derivative i) (AngularExpression.seed.derivative_remainder u j)
    ((literal_principal u).derivative j)

/-- Every genuine remainder jet has a uniform exponential bound in absolute log-height. -/
theorem gradientProductRemainder_jet_global_log_growth (u : ℂ) (i j : Fin 2) (word : List (Fin 2)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x k : ℝ,
      ‖coordinateJet word (gradientProductRemainder u i j) ![x,Real.exp k]‖ ≤ C * Real.exp (B * |k|) :=
  ((gradientProductRemainder_rapid u i j).jet word).global_log_growth

/-- Every actual gradient-product remainder jet has all complex height-weighted bounds. -/
theorem gradientProductRemainder_jet_weighted_bound (u w : ℂ) (i j : Fin 2)
    (word : List (Fin 2)) (l : Ioi (0:ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l.val ≤ z 1 →
      ‖(z 1:ℂ)^w * coordinateJet word (gradientProductRemainder u i j) z‖ ≤ C :=
  ((gradientProductRemainder_rapid u i j).jet word).bound w l.val l.property

/-- Every weighted gradient-product remainder jet vanishes along every horizontal path. -/
theorem gradientProductRemainder_jet_tendsto_zero (u w : ℂ) (i j : Fin 2)
    (word : List (Fin 2)) (X : ℝ → ℝ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w *
      coordinateJet word (gradientProductRemainder u i j) ![X y,y]) atTop (𝓝 0) :=
  ((gradientProductRemainder_rapid u i j).jet word).vanish w X

/-- The complete gradient-product remainder and all its coordinate jets are smooth. -/
theorem gradientProductRemainder_jet_smooth (u : ℂ) (i j : Fin 2)
    (word : List (Fin 2)) :
    ContDiffOn ℝ ∞ (coordinateJet word (gradientProductRemainder u i j)) domain :=
  ((gradientProductRemainder_rapid u i j).jet word).smooth

/-- The actual vertical Green flux for a full scalar test and one of the six
quartic contact fields, before any principal subtraction. -/
def quarticContactGreenFlux (q : XiZeroCopy) (slot : Fin 6) (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  scalar u z*coordDeriv 1 (quarticContactField q slot) z-
    quarticContactField q slot z*coordDeriv 1 (scalar u) z

/-- The vertical Green flux of both complete principal expressions. -/
def quarticContactPrincipalGreenFlux (q : XiZeroCopy) (slot : Fin 6) (u : ℂ)
    (z : Fin 2 → ℝ) : ℂ :=
  principal u z*coordDeriv 1 (quarticContactPrincipal q slot) z-
    quarticContactPrincipal q slot z*coordDeriv 1 (principal u) z

private theorem quarticContactGreenFlux_remainder_rapid (q : XiZeroCopy) (slot : Fin 6) (u : ℂ) :
    Rapid (fun z => quarticContactGreenFlux q slot u z-quarticContactPrincipalGreenFlux q slot u z) := by
  let e := quarticExpression (7*((center q)^2-1/4)-2) slot
  have ha := product_remainder_rapid (AngularExpression.seed.remainder u) (literal_principal u)
    (e.derivative_remainder (center q) 1) ((e.principal (center q)).derivative 1)
  have hb := product_remainder_rapid (e.remainder (center q)) (e.principal (center q))
    (AngularExpression.seed.derivative_remainder u 1) ((literal_principal u).derivative 1)
  apply (Rapid.add ha (Rapid.scale (-1) hb)).congr
  intro z hz
  change (scalar u z*coordDeriv 1 (quarticContactField q slot) z-
      principal u z*coordDeriv 1 (quarticContactPrincipal q slot) z)+
    (-1)*(quarticContactField q slot z*coordDeriv 1 (scalar u) z-
      quarticContactPrincipal q slot z*coordDeriv 1 (principal u) z)=_
  unfold quarticContactGreenFlux quarticContactPrincipalGreenFlux
  ring

private theorem Rapid.integral_vanish {f : Field} (hf : Rapid f) (w : ℂ) :
    Tendsto (fun y : ℝ => ∫ x in (-1/2:ℝ)..1/2, (y:ℂ)^w*f ![x,y]) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := hf.bound (w+1) 1 (by norm_num)
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [eventually_ge_atTop (max 1 (C/epsilon+1))] with y hy
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy1
  have hyC : C/epsilon+1 ≤ y := (le_max_right _ _).trans hy
  have hCy : C/y < epsilon := by
    apply (div_lt_iff₀ hy0).2
    have he : C/epsilon*epsilon=C := div_mul_cancel₀ C hepsilon.ne'
    nlinarith
  have hbound (x : ℝ) : ‖(y:ℂ)^w*f ![x,y]‖ ≤ C/y := by
    have heq : (y:ℂ)^w*f ![x,y]=((y:ℂ)^(w+1)*f ![x,y])/(y:ℂ) := by
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy0.ne'),Complex.cpow_one]
      field_simp [Complex.ofReal_ne_zero.mpr hy0.ne']
    rw [heq,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy0]
    exact div_le_div_of_nonneg_right (hb ![x,y] hy1) hy0.le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1/2:ℝ)) (b := (1/2:ℝ)) (fun x _ => hbound x)
  norm_num only [sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one] at hi
  rw [dist_zero_right]
  simpa only [neg_div] using hi.trans_lt hCy

/-- After subtraction of the complete original principal flux, the actual
integrated cusp boundary tends to zero with every complex height weight.
No individual principal contribution is set to zero. -/
theorem quarticContactGreenFlux_remainder_integral_tendsto_zero (q : XiZeroCopy)
    (slot : Fin 6) (u w : ℂ) :
    Tendsto (fun y : ℝ => ∫ x in (-1/2:ℝ)..1/2, (y:ℂ)^w*
      (quarticContactGreenFlux q slot u ![x,y]-quarticContactPrincipalGreenFlux q slot u ![x,y]))
      atTop (𝓝 0) :=
  (quarticContactGreenFlux_remainder_rapid q slot u).integral_vanish w

/-- Smoothness of the actual quartic fields on the entire positive-height chart. -/
theorem quarticContactField_smooth (q : XiZeroCopy) (slot : Fin 6) :
    ContDiffOn ℝ ∞ (quarticContactField q slot) domain :=
  (quarticExpression _ slot).smooth (center q) false

/-- Both unsubtracted cusp flux integrals exist at every positive height;
the limiting remainder theorem does not rely on a totalized undefined integral. -/
theorem quarticContactGreenFlux_intervalIntegrable (q : XiZeroCopy) (slot : Fin 6)
    (u : ℂ) (y : Ioi (0:ℝ)) :
    IntervalIntegrable (fun x : ℝ => quarticContactGreenFlux q slot u ![x,y.val])
        MeasureTheory.volume (-1/2) (1/2) ∧
      IntervalIntegrable (fun x : ℝ => quarticContactPrincipalGreenFlux q slot u ![x,y.val])
        MeasureTheory.volume (-1/2) (1/2) := by
  have hs : ContDiffOn ℝ ∞ (scalar u) domain := cuspLeg_contDiffOn .scalar u
  have hf := quarticContactField_smooth q slot
  have hp := (literal_principal u).smooth
  have hq := ((quarticExpression (7*((center q)^2-1/4)-2) slot).principal (center q)).smooth
  have hfull : ContinuousOn (quarticContactGreenFlux q slot u) domain :=
    ((hs.mul (derivative_smooth hf 1)).sub (hf.mul (derivative_smooth hs 1))).continuousOn
  have hprincipal : ContinuousOn (quarticContactPrincipalGreenFlux q slot u) domain :=
    ((hp.mul (derivative_smooth hq 1)).sub (hq.mul (derivative_smooth hp 1))).continuousOn
  have hc : Continuous (fun x : ℝ => ![x,y.val]) := by fun_prop
  have hmem : ∀ x : ℝ, ![x,y.val] ∈ domain := fun _ => y.property
  exact ⟨(hfull.comp_continuous hc hmem).intervalIntegrable _ _,
    (hprincipal.comp_continuous hc hmem).intervalIntegrable _ _⟩


open Complex UpperHalfPlane ModularGroup MeasureTheory
open scoped MatrixGroups ComplexConjugate
open GaloisForLFunctions.HTGeometry D4BMModularCore D4BMJointWave D4BMJointSource
set_option backward.isDefEq.respectTransparency false

private theorem coordinates_chart_smooth {f : Field} (hf : ContDiffOn ℝ ∞ f domain) :
    ChartSmooth (fun z => f (coordinates z)) := by
  intro z
  have hn : domain ∈ 𝓝 (coordinates z) :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds z.im_pos
  have hs := hf.contDiffAt hn
  have he : (fun z : UpperHalfPlane => f (coordinates z)) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      f ∘ angularCoordinates := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw,angularCoordinates]
    rfl
  exact (hs.comp (z:ℂ) angularCoordinates.contDiff.contDiffAt).congr_of_eventuallyEq he

private theorem AngularExpression.modular (e : AngularExpression) (q : XiZeroCopy) :
    ∀ γ : PSL2Z, ∀ z : UpperHalfPlane,
      e.eval (center q) false (coordinates (γ • z))=e.eval (center q) false (coordinates z) := by
  induction e with
  | seed =>
      intro γ z
      change scalar (center q) (coordinates (γ • z))=scalar (center q) (coordinates z)
      induction γ using QuotientGroup.induction_on with
      | H A => simpa only [PSL2Z_mk_smul] using xi_scalar_modular q A z
  | add f g hf hg => intro γ z; change _+_=_+_; rw [hf,hg]
  | mul f g hf hg => intro γ z; change _*_=_*_; rw [hf,hg]
  | scale c f hf => intro γ z; change c*_=c*_; rw [hf]
  | lap f hf =>
      intro γ z
      change hyperbolicLaplacian (f.eval (center q) false) (coordinates (γ • z))=
        hyperbolicLaplacian (f.eval (center q) false) (coordinates z)
      rw [← chartLaplacian_coordinates,← chartLaplacian_coordinates]
      exact chartLaplacian_invariant _ (coordinates_chart_smooth (f.smooth (center q) false)) hf γ z

/-- All six actual quartic contact expressions are modular scalars, including
both Laplacian terms and the retained fourth-order spin-two expression. -/
theorem quarticContactField_modular (q : XiZeroCopy) (slot : Fin 6) (γ : PSL2Z) (z : UpperHalfPlane) :
    quarticContactField q slot (coordinates (γ • z))=quarticContactField q slot (coordinates z) :=
  (quarticExpression _ slot).modular q γ z

private theorem cutoff_scale_one_le (n : ℕ) : (1:ℝ) ≤ (n:ℝ)+1 := by
  have hn : (0:ℝ) ≤ n := by positivity
  linarith

/-- A constructed original modular core field for each complete quartic source,
using the existing scale-n+1 cusp cutoff. -/
def quarticContactCoreCutoff (q : XiZeroCopy) (slot : Fin 6) (n : ℕ) : CoreField where
  field z := modularCuspCutoff ((n:ℝ)+1) z*quarticContactField q slot (coordinates z)
  smooth z := (modularCuspCutoff_smooth _ (cutoff_scale_one_le n) z).mul
    (coordinates_chart_smooth (quarticContactField_smooth q slot) z)
  invariant γ z := by rw [modularCuspCutoff_invariant _ (cutoff_scale_one_le n),quarticContactField_modular]
  compact := by
    obtain ⟨K,hK,hc⟩ := modularCuspCutoff_compact ((n:ℝ)+1) (cutoff_scale_one_le n)
    refine ⟨K,hK,?_⟩
    intro z hz hn
    change modularCuspCutoff ((n:ℝ)+1) z*_ = 0
    rw [hc z hz hn,zero_mul]

private theorem quartic_core_zero_germ (q : XiZeroCopy) (slot : Fin 6) (n : ℕ)
    (z : UpperHalfPlane) (hz : z ∈ fd) (hy : 3*((n:ℝ)+1) < z.im) :
    (quarticContactCoreCutoff q slot n).field =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [modularCuspCutoff_germ _ (cutoff_scale_one_le n) z hz,
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds hy] with w hw hwy
  change modularCuspCutoff ((n:ℝ)+1) w*_ = 0
  rw [hw,scaledCuspCutoff_high _ _ (by positivity) hwy.le,Complex.ofReal_zero,zero_mul]

private theorem outer_physical_test_germ (r : XiZeroCopy) (n : ℕ) (z : UpperHalfPlane)
    (hz : z ∈ fd) (hy : z.im ≤ 3*((n:ℝ)+1)) :
    (physicalCoreCutoff r (3*n+2)).field =ᶠ[𝓝 z] physicalTestField r := by
  have hy' : z.im < 2*(((3*n+2:ℕ):ℝ)+1) := by
    push_cast
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  filter_upwards [modularCuspCutoff_germ _ (cutoff_scale_one_le (3*n+2)) z hz,
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hy'] with w hw hwy
  change modularCuspCutoff (((3*n+2:ℕ):ℝ)+1) w*physicalTestField r w=physicalTestField r w
  rw [hw,scaledCuspCutoff_low _ _ (by positivity) hwy.le,Complex.ofReal_one,one_mul]

private theorem core_inner_integral (f g : CoreField) :
    Integrable (fun z => conj (f.field z)*g.field z) D4BMModularCore.measure ∧
    inner ℂ (fieldVector f) (fieldVector g) =
      ∫ z, conj (f.field z)*g.field z ∂D4BMModularCore.measure := by
  have he : (fun z => inner ℂ (fieldVector f z) (fieldVector g z)) =ᵐ[D4BMModularCore.measure]
      (fun z => conj (f.field z)*g.field z) := by
    filter_upwards [(core_field_memLp f.field f.smooth f.compact).coeFn_toLp,
      (core_field_memLp g.field g.smooth g.compact).coeFn_toLp] with z hf hg
    change fieldVector f z = _ at hf
    change fieldVector g z = _ at hg
    rw [hf,hg]
    simp only [RCLike.inner_apply,mul_comm]
  exact ⟨(L2.integrable_inner (𝕜 := ℂ) (fieldVector f) (fieldVector g)).congr he,
    (L2.inner_def _ _).trans (integral_congr_ae he)⟩

private theorem core_second_green (f g : CoreField) :
    inner ℂ (fieldVector f.laplacian) (fieldVector g) =
      inner ℂ (fieldVector f) (fieldVector g.laplacian) := by
  have hf := f.completed_green ⟨frameGraph g,frameGraph_mem g⟩
  have hg := g.completed_green ⟨frameGraph f,frameGraph_mem f⟩
  change inner ℂ (derivativeVector f 1) (derivativeVector g 1)+
    inner ℂ (derivativeVector f Complex.I) (derivativeVector g Complex.I) =
      -inner ℂ (fieldVector f.laplacian) (fieldVector g) at hf
  change inner ℂ (derivativeVector g 1) (derivativeVector f 1)+
    inner ℂ (derivativeVector g Complex.I) (derivativeVector f Complex.I) =
      -inner ℂ (fieldVector g.laplacian) (fieldVector f) at hg
  have hc := congrArg conj hg
  simp only [map_add,map_neg,inner_conj_symm] at hc
  exact neg_injective (hf.symm.trans hc)

/-- The actual physical QNM angular test transposes against every constructed
quartic source cutoff. All modular seams are included by the original core
Green theorem; no test-domain or Green identity premise is supplied. -/
theorem quarticContactCoreCutoff_physical_green (q r : XiZeroCopy) (slot : Fin 6) (n : ℕ) :
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter r) (coordinates z)*
      (quarticContactCoreCutoff q slot n).field z) D4BMModularCore.measure ∧
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter r) (coordinates z)*
      (quarticContactCoreCutoff q slot n).laplacian.field z) D4BMModularCore.measure ∧
    (∫ z : UpperHalfPlane, scalar (physicalAngularParameter r) (coordinates z)*
      (quarticContactCoreCutoff q slot n).laplacian.field z ∂D4BMModularCore.measure) =
      (physicalAngularParameter r^2-1/4)*∫ z : UpperHalfPlane,
        scalar (physicalAngularParameter r) (coordinates z)*
          (quarticContactCoreCutoff q slot n).field z ∂D4BMModularCore.measure := by
  let F := physicalCoreCutoff r (3*n+2)
  let G := quarticContactCoreCutoff q slot n
  have hzero (z : UpperHalfPlane) (hz : z ∈ fd) (hy : 3*((n:ℝ)+1)<z.im) :
      G.field z=0 ∧ G.laplacian.field z=0 := by
    have he := quartic_core_zero_germ q slot n z hz hy
    refine ⟨he.eq_of_nhds,?_⟩
    rw [CoreField.laplacian_field,chartLaplacian_congr he]
    simp [chartLaplacian,planarLaplacian,Function.comp_def]
  have he₀ : (fun z => conj (F.field z)*G.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => scalar (physicalAngularParameter r) (coordinates z)*G.field z) := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    by_cases hy : z.im ≤ 3*((n:ℝ)+1)
    · rw [(outer_physical_test_germ r n z hz hy).eq_of_nhds]
      simp only [physicalTestField,starRingEnd_self_apply]
    · rw [(hzero z hz (lt_of_not_ge hy)).1,mul_zero,mul_zero]
  have he₁ : (fun z => conj (F.laplacian.field z)*G.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => (physicalAngularParameter r^2-1/4)*
        (scalar (physicalAngularParameter r) (coordinates z)*G.field z)) := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    by_cases hy : z.im ≤ 3*((n:ℝ)+1)
    · rw [CoreField.laplacian_field,
        chartLaplacian_congr (outer_physical_test_germ r n z hz hy),
        physicalTestField_laplacian,starRingEnd_self_apply,mul_assoc]
    · rw [(hzero z hz (lt_of_not_ge hy)).1,mul_zero,mul_zero,mul_zero]
  have he₂ : (fun z => conj (F.field z)*G.laplacian.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => scalar (physicalAngularParameter r) (coordinates z)*G.laplacian.field z) := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    by_cases hy : z.im ≤ 3*((n:ℝ)+1)
    · rw [(outer_physical_test_germ r n z hz hy).eq_of_nhds]
      simp only [physicalTestField,starRingEnd_self_apply]
    · rw [(hzero z hz (lt_of_not_ge hy)).2,mul_zero,mul_zero]
  have h₀ := core_inner_integral F G
  have h₁ := core_inner_integral F.laplacian G
  have h₂ := core_inner_integral F G.laplacian
  refine ⟨h₀.1.congr he₀,h₂.1.congr he₂,?_⟩
  change (∫ z, scalar (physicalAngularParameter r) (coordinates z)*G.laplacian.field z
    ∂D4BMModularCore.measure)=_
  rw [← integral_congr_ae he₂,← h₂.2,← core_second_green F G,h₁.2,
    integral_congr_ae he₁,integral_const_mul]

/-- Every source cutoff retains both its first- and second-height derivative
terms in the actual modular Laplacian on the original closed cell. -/
theorem quarticContactCoreCutoff_laplacian (q : XiZeroCopy) (slot : Fin 6) (n : ℕ)
    (z : {z : UpperHalfPlane // z ∈ fd}) :
    (quarticContactCoreCutoff q slot n).laplacian.field z.val =
      (scaledCuspCutoff ((n:ℝ)+1) z.val.im:ℂ)*
        hyperbolicLaplacian (quarticContactField q slot) (coordinates z.val)+
      2*(z.val.im:ℂ)^2*((deriv (scaledCuspCutoff ((n:ℝ)+1)) z.val.im:ℝ):ℂ)*
        coordDeriv 1 (quarticContactField q slot) (coordinates z.val)+
      (z.val.im:ℂ)^2*((deriv (deriv (scaledCuspCutoff ((n:ℝ)+1))) z.val.im:ℝ):ℂ)*
        quarticContactField q slot (coordinates z.val) := by
  have he : (quarticContactCoreCutoff q slot n).field =ᶠ[𝓝 z.val] fun w =>
      (scaledCuspCutoff ((n:ℝ)+1) w.im:ℂ)*quarticContactField q slot (coordinates w) := by
    filter_upwards [modularCuspCutoff_germ _ (cutoff_scale_one_le n) z.val z.property] with w hw
    change modularCuspCutoff ((n:ℝ)+1) w*_= _
    rw [hw]
  rw [CoreField.laplacian_field,chartLaplacian_congr he]
  change chartLaplacian (fun w =>
    (fun x : Fin 2 → ℝ => (scaledCuspCutoff ((n:ℝ)+1) (x 1):ℂ)*
      quarticContactField q slot x) (coordinates w)) z.val = _
  rw [chartLaplacian_coordinates (fun x : Fin 2 → ℝ =>
      (scaledCuspCutoff ((n:ℝ)+1) (x 1):ℂ)*quarticContactField q slot x) z.val]
  have hn : domain ∈ 𝓝 (coordinates z.val) :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds z.val.im_pos
  have hf : ContDiffAt ℝ 2 (quarticContactField q slot) (coordinates z.val) :=
    ((quarticContactField_smooth q slot).contDiffAt hn).of_le (by norm_cast)
  exact hyperbolicLaplacian_height_mul _ (scaledCuspCutoff_smooth _) _ _ hf

end
end RHTower.D4BMSquareCuspJets
