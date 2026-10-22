import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThreeFieldReconstruction

/-! Exact differential lifting of the original three radial columns. -/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.TwistedRadial
open scoped ContDiff
namespace RHTower.D4BMThreeFieldRows
open D4BMScalarStream D4BMScalarSourceIdentification D4BMThreeFieldReconstruction
noncomputable section
set_option autoImplicit false

private theorem twist_three (s a b : ℂ) {f g h : ℝ → ℂ} {r : ℝ}
    (hf : DifferentiableAt ℝ f r) (hg : DifferentiableAt ℝ g r)
    (hh : DifferentiableAt ℝ h r) :
    twist s (fun t => f t+g t/a+h t/b) r =
      twist s f r+twist s g r/a+twist s h r/b := by
  have hd := ((hf.hasDerivAt.add (hg.hasDerivAt.div_const a)).add
    (hh.hasDerivAt.div_const b)).deriv
  change deriv (fun t => f t+g t/a+h t/b) r = _ at hd
  unfold twist
  rw [hd]
  ring

/-- All actual twisted jets retain the exact three-field decomposition. -/
theorem original_twistIter_three (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    (n : ℕ) {r : ℝ} (hr1 : 1 < r) (j : Fin 4) :
    twistIter s n (originalRadialColumn s μ j) r =
      twistIter s n (radialColumn s 0 j) r+
      twistIter s n (radialColumn s 1 j) r/(2-μ)+
      twistIter s n (radialColumn s 2 j) r/(μ-targetShift s) := by
  induction n generalizing r with
  | zero => exact originalRadialColumn_three_fields s μ hs hμ hres hshift hr1 j
  | succ n ih =>
    have he : twistIter s n (originalRadialColumn s μ j) =ᶠ[𝓝 r] (fun t =>
        twistIter s n (radialColumn s 0 j) t+twistIter s n (radialColumn s 1 j) t/(2-μ)+
        twistIter s n (radialColumn s 2 j) t/(μ-targetShift s)) := by
      filter_upwards [exterior_eventually hr1] with t ht
      exact ih ht
    rw [twistIter_succ,twist_congr s he]
    exact twist_three s (2-μ) (μ-targetShift s)
      (differentiableAt_twistIter s (radialColumn_smooth s 0 j) n hr1)
      (differentiableAt_twistIter s (radialColumn_smooth s 1 j) n hr1)
      (differentiableAt_twistIter s (radialColumn_smooth s 2 j) n hr1)

/-- Values and first two actual twisted derivatives of four radial amplitudes. -/
abbrev RowJet := Fin 4 → Fin 3 → ℂ

def radialJets (s : ℂ) (F : Fin 4 → ℝ → ℂ) (r : ℝ) : RowJet :=
  fun j n => twistIter s n (F j) r

def rowOperator (s r μ : ℂ) (i : Fin 7) (J : RowJet) : ℂ :=
  ![harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL] i
    s r μ (J 0 0) (J 0 1) (J 0 2) (J 1 0) (J 1 1) (J 1 2)
    (J 2 0) (J 2 1) (J 2 2) (J 3 0) (J 3 1) (J 3 2)

/-- Every original Einstein row is affine in the angular spectral parameter. -/
theorem rowOperator_affine (s r μ : ℂ) (i : Fin 7) (J : RowJet) :
    rowOperator s r μ i J = rowOperator s r 0 i J+
      μ*(rowOperator s r 1 i J-rowOperator s r 0 i J) := by
  fin_cases i <;> simp [rowOperator,harmonicTT,harmonicTR,harmonicRR,harmonicT,
    harmonicR,harmonicTF,harmonicL,div_eq_mul_inv] <;> ring

/-- The same rows act linearly on the three original radial-jet columns. -/
theorem rowOperator_three (s r μ a b : ℂ) (i : Fin 7) (J : Fin 3 → RowJet) :
    rowOperator s r μ i (fun j n => J 0 j n+J 1 j n/a+J 2 j n/b) =
      rowOperator s r μ i (J 0)+rowOperator s r μ i (J 1)/a+
        rowOperator s r μ i (J 2)/b := by
  fin_cases i <;> simp [rowOperator,harmonicTT,harmonicTR,harmonicRR,harmonicT,
    harmonicR,harmonicTF,harmonicL,div_eq_mul_inv] <;> ring

def sourceRows (s r μ : ℂ) : Fin 7 → ℂ :=
  ![ssSourceTT s r μ,ssSourceTR s r μ,ssSourceRR s r μ,ssSourceT s r μ,
    ssSourceR s r μ,ssSourceTF s r μ,ssSourceL s r μ]

def sourceConstant (s r : ℂ) : Fin 7 → ℂ :=
  ![ssSourceTT s r 0,ssSourceTR s r 0,ssSourceRR s r 0,ssSourceT s r 0,
    ssSourceR s r 0,tensorCoefficient s r,ssSourceL s r 0]

def sourceSlope (s r : ℂ) : Fin 7 → ℂ :=
  ![ssSourceTT s r 1-ssSourceTT s r 0,0,ssSourceRR s r 1-ssSourceRR s r 0,
    0,0,0,ssSourceL s r 1-ssSourceL s r 0]

def sourceResidue (s r : ℂ) : Fin 7 → ℂ :=
  ![0,0,0,0,0,(s+1)*(s+2)*tensorCoefficient s r,0]

/-- Exact constant, differential and shift-two parts of the original retained source. -/
theorem sourceRows_expansion (s r μ : ℂ) (hr : r ≠ 0) (hμ : 2-μ ≠ 0) (i : Fin 7) :
    sourceRows s r μ i = sourceConstant s r i+μ*sourceSlope s r i+sourceResidue s r i/(2-μ) := by
  fin_cases i <;> simp [sourceRows,sourceConstant,sourceSlope,sourceResidue,
    ssSourceTF_factor s r μ hr hμ,ssSourceTT,ssSourceTR,ssSourceRR,ssSourceT,
    ssSourceR,ssSourceL,div_eq_mul_inv] <;> ring

/-- Polynomial rigidity for the four residual coefficients, proved by exact interpolation. -/
theorem residual_coefficients_zero (d A B C D : ℂ) (hshift : 2-d ≠ 0)
    (hden : ∀ n : Fin 4, -(n:ℂ)-d ≠ 0)
    (h : ∀ n : Fin 4, -(n:ℂ)*A+B+C/(2+(n:ℂ))+D/(-(n:ℂ)-d) = 0) :
    A=0 ∧ B=0 ∧ C=0 ∧ D=0 := by
  have clear (n : Fin 4) :
      (-(n:ℂ)*A+B)*(2+(n:ℂ))*(-(n:ℂ)-d)+C*(-(n:ℂ)-d)+D*(2+(n:ℂ)) = 0 := by
    have hv := h n
    have hnd := hden n
    have hn : 2+(n:ℂ) ≠ 0 := by
      exact_mod_cast (show (2:ℝ)+(n:ℝ) ≠ 0 by positivity)
    field_simp at hv
    linear_combination hv
  have h0 := clear 0
  have h1 := clear 1
  have h2 := clear 2
  have h3 := clear 3
  norm_num at h0 h1 h2 h3
  have hA : A=0 := by linear_combination (-h0+3*h1-3*h2+h3)/6
  subst A
  have hB : B=0 := by linear_combination (-h0+2*h1-h2)/2
  subst B
  have hc : (2-d)*C=0 := by linear_combination 3*h0-2*h1
  have hC := (mul_eq_zero.mp hc).resolve_left hshift
  refine ⟨rfl,rfl,hC,?_⟩
  linear_combination h0/2+d*hC/2


def operatorSlope (s r : ℂ) (i : Fin 7) (J : RowJet) : ℂ :=
  rowOperator s r 1 i J-rowOperator s r 0 i J

/-- Four coefficients of the exact residual after the two angular poles are separated. -/
def rowCoefficients (s r : ℂ) (i : Fin 7) (J : Fin 3 → RowJet) : Fin 4 → ℂ :=
  ![operatorSlope s r i (J 0)+sourceSlope s r i,
    rowOperator s r 0 i (J 0)-operatorSlope s r i (J 1)+operatorSlope s r i (J 2)+
      sourceConstant s r i,
    rowOperator s r 0 i (J 1)+2*operatorSlope s r i (J 1)+sourceResidue s r i,
    rowOperator s r 0 i (J 2)+targetShift s*operatorSlope s r i (J 2)]

/-- Exact four-coefficient form of every original sourced row. -/
theorem rowResidual_expansion (s r μ : ℂ) (hr : r ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) (i : Fin 7) (J : Fin 3 → RowJet) :
    rowOperator s r μ i (fun j n => J 0 j n+J 1 j n/(2-μ)+J 2 j n/(μ-targetShift s))+
      sourceRows s r μ i =
      μ*rowCoefficients s r i J 0+rowCoefficients s r i J 1+
        rowCoefficients s r i J 2/(2-μ)+rowCoefficients s r i J 3/(μ-targetShift s) := by
  rw [rowOperator_three,sourceRows_expansion s r μ hr hμ i,
    rowOperator_affine s r μ i (J 0),rowOperator_affine s r μ i (J 1),
    rowOperator_affine s r μ i (J 2)]
  simp only [rowCoefficients,operatorSlope,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  field_simp
  ring

/-- The seven original sourced Einstein equations hold for the actual reconstructed radial jets. -/
theorem original_rows_zero (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) {r : ℝ} (hr1 : 1 < r) (i : Fin 7) :
    rowOperator s r μ i (radialJets s (originalRadialColumn s μ) r)+sourceRows s r μ i = 0 := by
  have h := ssLaurentMaster_sourcedData s μ hs hμ hres
  fin_cases i <;> simp [rowOperator,sourceRows,radialJets,originalRadialColumn,
    originalF0,originalF1,originalF2,originalH,twistIter_zero,twistIter_succ]
  · simpa only [srcTT_eq s μ hr1 hs hμ] using sourced_equation_TT hs hμ h hr1
  · simpa only [srcTR_eq s μ hr1 hs hμ] using sourced_equation_TR hs hμ h hr1
  · simpa only [srcRR_eq s μ hr1 hs hμ] using sourced_equation_RR hs hμ h hr1
  · simpa only [srcT_eq s μ hr1 hs hμ] using sourced_equation_T hs hμ h hr1
  · simpa only [srcR_eq s μ hr1 hs hμ] using sourced_equation_R hs hμ h hr1
  · simpa only [srcTF_eq s μ hr1 hs hμ] using sourced_equation_TF hs hμ h hr1
  · simpa only [srcL_eq s μ hr1 hs hμ] using sourced_equation_L hs hμ h hr1

/-- The original sourced equations vanish in the four-pole basis of the actual three radial columns. -/
theorem actual_rowResidual_zero (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) (i : Fin 7) :
    let C := rowCoefficients s r i (fun k => radialJets s (radialColumn s k) r)
    μ*C 0+C 1+C 2/(2-μ)+C 3/(μ-targetShift s) = 0 := by
  have h := original_rows_zero s μ hs hμ hres hr1 i
  have hj : radialJets s (originalRadialColumn s μ) r =
      (fun j n => radialJets s (radialColumn s 0) r j n+
        radialJets s (radialColumn s 1) r j n/(2-μ)+
        radialJets s (radialColumn s 2) r j n/(μ-targetShift s)) := by
    funext j n
    exact original_twistIter_three s μ hs hμ hres hshift n hr1 j
  rw [hj,rowResidual_expansion s r μ (exterior_ne r hr1).1 hμ hres i
    (fun k => radialJets s (radialColumn s k) r)] at h
  exact h

/-- All twenty-eight required differential coefficient equations hold for the actual physical columns. -/
theorem physical_rowCoefficients_zero (q : XiZeroCopy) (branch : Bool)
    {r : ℝ} (hr1 : 1 < r) (i : Fin 7) (j : Fin 4) :
    rowCoefficients (D4BMModularCore.physicalRate q branch) r i
      (fun k => radialJets (D4BMModularCore.physicalRate q branch)
        (radialColumn (D4BMModularCore.physicalRate q branch) k) r) j = 0 := by
  let s := D4BMModularCore.physicalRate q branch
  let C := rowCoefficients s r i (fun k => radialJets s (radialColumn s k) r)
  obtain ⟨hs,_,hshift⟩ := physical_shifts q branch
  obtain ⟨hre,him⟩ := physicalLaurentRate_bounds q branch
  have hd (n : Fin 4) : -(n:ℂ)-targetShift s ≠ 0 := by
    have he := laurentPole_ne_zero s hre him (-(n:ℝ))
    push_cast at he
    exact he
  have hv (n : Fin 4) : -(n:ℂ)*C 0+C 1+C 2/(2+(n:ℂ))+C 3/(-(n:ℂ)-targetShift s)=0 := by
    have hμ : (2:ℂ)-(-(n:ℂ)) ≠ 0 := by
      exact_mod_cast (show (2:ℝ)-(-(n:ℝ)) ≠ 0 by rw [sub_neg_eq_add]; positivity)
    simpa only [sub_neg_eq_add] using actual_rowResidual_zero s (-(n:ℂ)) hs hμ (hd n) hshift hr1 i
  obtain ⟨h0,h1,h2,h3⟩ := residual_coefficients_zero (targetShift s) (C 0) (C 1) (C 2) (C 3) hshift hd hv
  change C j=0
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end
end RHTower.D4BMThreeFieldRows
