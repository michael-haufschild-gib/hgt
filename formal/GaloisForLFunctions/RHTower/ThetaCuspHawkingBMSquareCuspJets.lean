import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMWeightedSquareCuspBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularScalarEquation

/-! Every actual coordinate jet of the full squared-source cusp remainder has
all complex height-weighted bounds. The proof differentiates the complete
signed Fourier–Bessel family and retains both principal–tail cross terms. -/

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

/-- Every genuine coordinate jet of the complete squared-source remainder is
bounded after any complex height weight, uniformly over the whole half-strip. -/
theorem squareRemainder_jet_weighted_bound (u w : ℂ) (word : List (Fin 2)) (l : Ioi (0:ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l.val ≤ z 1 →
      ‖(z 1:ℂ)^w * coordinateJet word (squareRemainder u) z‖ ≤ C :=
  ((squareRemainder_rapid u).jet word).bound w l.val l.property

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

end
end RHTower.D4BMSquareCuspJets

