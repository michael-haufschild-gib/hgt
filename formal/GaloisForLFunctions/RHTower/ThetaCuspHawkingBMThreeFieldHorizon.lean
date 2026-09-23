import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMThreeFieldReconstruction

/-!
# Exact ingoing extension of the original three-field radial reconstruction

The original angular metric coefficients are finite Laurent polynomials. Their exact
source-retaining horizon residue vanishes in each of the three columns. The original
coordinate transformation therefore gives explicit ingoing radial amplitudes smooth at
every positive radius, including the horizon. Actual exterior derivatives and both physical
branches are retained. This proves radial extension of the particular reconstruction;
the nonseparated Einstein equation, retarded onset, boundary admission and left-QNM action
remain separate obligations.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.TwistedRadial
open scoped ContDiff
namespace RHTower.D4BMThreeFieldHorizon
open D4BMScalarStream D4BMScalarSourceIdentification D4BMThreeFieldReconstruction
noncomputable section
set_option autoImplicit false

/-- Physical-shift Laurent constant after the horizon denominator cancels. -/
def regularHDCoefficient (s : ℂ) : ℂ := 3*(s+1)^(2 : ℕ)*(3*s+4)/(8*(2*s+3))

/-- Three Laurent constants of the angular metric amplitudes, regular at the horizon. -/
def angularLaurentA (s : ℂ) : Fin 3 → ℂ :=
  ![1/4,regularHDCoefficient s-(3*s^(2 : ℕ)+6*s+2)/4,regularHDCoefficient s]

/-- Three inverse-square Laurent coefficients of the angular metric amplitudes. -/
def angularLaurentB (s : ℂ) : Fin 3 → ℂ :=
  ![s*(3*s+2)/8,regularHDCoefficient s*(2*s^(2 : ℕ)+s)-s*(4*s^(3 : ℕ)+9*s^(2 : ℕ)+6*s+2)/4,
    regularHDCoefficient s*(2*s^(2 : ℕ)+s)]

/-- Three inverse-fourth Laurent coefficients of the angular metric amplitudes. -/
def angularLaurentC (s : ℂ) : Fin 3 → ℂ :=
  ![s^(2 : ℕ)*(s+1)^(2 : ℕ)/32,-s^(2 : ℕ)*(s+1)^(3 : ℕ)/16,0]

/-- Horizon-regular expression of each original angular metric amplitude. -/
def regularAngularColumn (s : ℂ) (k : Fin 3) (r : ℂ) : ℂ :=
  angularLaurentA s k+angularLaurentB s k/r^(2 : ℕ)+angularLaurentC s k/r^(4 : ℕ)

/-- The original angular coefficients lose every apparent horizon denominator. -/
theorem angular_column_laurent (s : ℂ) (hs : s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) (k : Fin 3) :
    radialColumn s k 3 r = regularAngularColumn s k r := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  have hd : 2*s+3 ≠ 0 := by
    intro he
    apply hshift
    unfold targetShift
    linear_combination (-2*s)*he
  have hfactor : 2-targetShift s = -2*s*(2*s+3) := by unfold targetShift; ring
  have hdn : 3+s*2 ≠ 0 := by simpa [add_comm,mul_comm] using hd
  have hden : 24+s*16 ≠ 0 := by
    intro he
    apply hd
    linear_combination he/8
  fin_cases k <;> simp only [radialColumn,regularAngularColumn,angularLaurentA,
    angularLaurentB,angularLaurentC,Matrix.cons_val',Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,
    Matrix.tail_cons,Fin.reduceFinMk]
  all_goals simp only [metricH0,metricH2,metricHD,reducedMaster01,reducedMasterD1,
    reducedMaster0,reducedMasterD,regularHDCoefficient,hfactor,ssSourceTR,ssSourceT]
  all_goals field_simp
  all_goals try unfold targetShift
  all_goals ring

/-- The reduced master has these three first Laurent coefficients. -/
def masterLeading : Fin 3 → ℂ := ![1,0,0]
def masterInverse (s : ℂ) : Fin 3 → ℂ := ![s*(3*s+2)/2,0,3*s*(s+1)^(2 : ℕ)*(3*s+4)/2]
def masterInverseCube (s : ℂ) : Fin 3 → ℂ := ![s^(2 : ℕ)*(s+1)^(2 : ℕ)/8,0,0]
def tensorWeight (s : ℂ) : Fin 3 → ℂ := ![1,(s+1)*(s+2),0]

def wLeading (s : ℂ) (k : Fin 3) : ℂ := 4*angularLaurentA s k-masterLeading k
def wInverse (s : ℂ) (k : Fin 3) : ℂ := 4*angularLaurentB s k-masterInverse s k
def wInverseCube (s : ℂ) (k : Fin 3) : ℂ := 4*angularLaurentC s k-masterInverseCube s k

def pInverseSquare (s : ℂ) (k : Fin 3) : ℂ :=
  -8*angularLaurentB s k+masterInverse s k+masterLeading k*s*(s+2)/2+
    tensorWeight s k*s^(2 : ℕ)

def pInverseFourth (s : ℂ) (k : Fin 3) : ℂ :=
  -16*angularLaurentC s k+3*masterInverseCube s k+
    masterLeading k*3*s^(2 : ℕ)*(s+1)^(2 : ℕ)/8-tensorWeight s k*s^(2 : ℕ)*(s+1)^(2 : ℕ)/4

/-- Each original column has precisely the residue cancellation required at the ingoing horizon. -/
theorem horizon_numerator_zero (s : ℂ) (hs : 2*s+3 ≠ 0) (k : Fin 3) :
    pInverseSquare s k+pInverseFourth s k =
      s*(wLeading s k+wInverse s k+wInverseCube s k) := by
  have hc : (8*(2*s+3))*regularHDCoefficient s = 3*(s+1)^(2 : ℕ)*(3*s+4) :=
    mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hs)
  fin_cases k <;> simp only [pInverseSquare,pInverseFourth,wLeading,wInverse,wInverseCube,
    angularLaurentA,angularLaurentB,angularLaurentC,masterLeading,masterInverse,masterInverseCube,
    tensorWeight,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Fin.reduceFinMk]
  all_goals generalize regularHDCoefficient s = C at hc ⊢
  · ring
  · linear_combination -(s*(s+1)/2)*hc
  · linear_combination -(s*(s+1)/2)*hc

/-- Explicit ingoing radial coefficient after dividing out the vanishing horizon numerator. -/
def regularIngoingRR (s : ℂ) (k : Fin 3) (r : ℂ) : ℂ :=
  (-2*s*wLeading s k*r^(3 : ℕ)+(pInverseSquare s k-2*s*wLeading s k)*r^(2 : ℕ)+
    (-2*pInverseFourth s k+2*s*wInverseCube s k)*r+
    (-pInverseFourth s k+2*s*wInverseCube s k))/(r^(4 : ℕ)*(r+1)^(2 : ℕ))

/-- The remaining radial pole cancels exactly, retaining the full source contribution. -/
theorem horizon_numerator_factor (s r : ℂ) (hs : 2*s+3 ≠ 0)
    (hr : r ≠ 0) (hp : r+1 ≠ 0) (k : Fin 3) :
    pInverseSquare s k/r^(2 : ℕ)+pInverseFourth s k/r^(4 : ℕ)-
      2*s/(r+1)*(wLeading s k+wInverse s k/r^(2 : ℕ)+wInverseCube s k/r^(4 : ℕ)) =
      (r^(2 : ℕ)-1)*regularIngoingRR s k r := by
  have he := horizon_numerator_zero s hs k
  unfold regularIngoingRR
  field_simp
  linear_combination 2*r^(2 : ℕ)*(r+1)*he

/-- The divided radial expression is smooth through every positive radius, including the horizon. -/
theorem regularIngoingRR_smooth (s : ℂ) (k : Fin 3) {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ∞ (fun t : ℝ => regularIngoingRR s k t) r := by
  have h0 : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hp : (r:ℂ)+1 ≠ 0 := by exact_mod_cast (show r+1 ≠ 0 by linarith)
  unfold regularIngoingRR
  simp only [div_eq_mul_inv,mul_inv]
  fun_prop (disch := aesop)


/-- The Laurent expression has its genuine ordinary radial derivative. -/
theorem regularAngularColumn_hasDerivAt (s : ℂ) (k : Fin 3) {r : ℝ}
    (hr : (r:ℂ) ≠ 0) :
    HasDerivAt (fun t : ℝ => regularAngularColumn s k t)
      (-2*angularLaurentB s k/(r:ℂ)^(3 : ℕ)-4*angularLaurentC s k/(r:ℂ)^(5 : ℕ)) r := by
  have hR : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have h := ((hasDerivAt_const r (angularLaurentA s k)).add
    ((hasDerivAt_const r (angularLaurentB s k)).div (hR.pow 2) (pow_ne_zero 2 hr))).add
    ((hasDerivAt_const r (angularLaurentC s k)).div (hR.pow 4) (pow_ne_zero 4 hr))
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The original exterior twisted derivative equals the derivative of its regular Laurent expression. -/
theorem angular_column_twist (s : ℂ) (hs : s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) (k : Fin 3) :
    twist s (radialColumn s k 3) r =
      -2*angularLaurentB s k/(r:ℂ)^(3 : ℕ)-4*angularLaurentC s k/(r:ℂ)^(5 : ℕ)+
        2*s/(r*((r:ℂ)^(2 : ℕ)-1))*regularAngularColumn s k r := by
  have he : radialColumn s k 3 =ᶠ[𝓝 r] (fun t : ℝ => regularAngularColumn s k t) := by
    filter_upwards [exterior_eventually hr1] with t ht
    exact angular_column_laurent s hs hshift ht k
  rw [twist_congr s he]
  exact congrArg (fun v => v+2*s/(r*((r:ℂ)^(2 : ℕ)-1))*regularAngularColumn s k r)
    (regularAngularColumn_hasDerivAt s k (exterior_ne r hr1).1).deriv

/-- The actual radial-radial coefficient after the original ingoing coordinate change has no horizon pole. -/
theorem original_ingoing_rr (s : ℂ) (hs : s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) (k : Fin 3) :
    radialColumn s k 2 r-2*radialColumn s k 1 r/((r:ℂ)^(2 : ℕ)-1)+
      radialColumn s k 0 r/((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ) = regularIngoingRR s k r := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  have hp : (r:ℂ)+1 ≠ 0 := by exact_mod_cast (show r+1 ≠ 0 by linarith)
  have hd : 2*s+3 ≠ 0 := by
    intro he
    apply hshift
    unfold targetShift
    linear_combination (-2*s)*he
  have hdn : 3+s*2 ≠ 0 := by simpa [add_comm,mul_comm] using hd
  have hden : 24+s*16 ≠ 0 := by
    intro he
    apply hd
    linear_combination he/8
  have h0 := angular_column_laurent s hs hshift hr1 0
  have h2 := angular_column_laurent s hs hshift hr1 1
  have hD := angular_column_laurent s hs hshift hr1 2
  have ht0 := angular_column_twist s hs hshift hr1 0
  have ht2 := angular_column_twist s hs hshift hr1 1
  have htD := angular_column_twist s hs hshift hr1 2
  simp only [radialColumn,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    at h0 h2 hD ht0 ht2 htD
  fin_cases k <;> simp only [radialColumn,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Fin.reduceFinMk,
    metricF00,metricF02,metricF0D,metricF20,metricF22,metricF2D,metricF12,metricF1D]
  all_goals simp only [h0,h2,hD,ht0,ht2,htD]
  · simp only [regularIngoingRR,pInverseSquare,pInverseFourth,wLeading,wInverseCube,
    regularAngularColumn,angularLaurentA,angularLaurentB,angularLaurentC,masterLeading,
    masterInverse,masterInverseCube,tensorWeight,regularHDCoefficient,reducedMasterD,
    tensorCoefficient,ssSourceTR,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    field_simp
    ring

  · have hfac := horizon_numerator_factor s (r:ℂ) hd hr hp 1
    simp only [pInverseSquare,pInverseFourth,wLeading,wInverse,wInverseCube,
      masterLeading,masterInverse,masterInverseCube,tensorWeight,regularAngularColumn,tensorCoefficient,
      Matrix.cons_val_zero,Matrix.cons_val_one,
      ] at hfac ⊢
    linear_combination (norm := (field_simp; ring)) hfac/((r:ℂ)^(2 : ℕ)-1)
  · simp only [regularIngoingRR,pInverseSquare,pInverseFourth,wLeading,wInverseCube,
    regularAngularColumn,angularLaurentA,angularLaurentB,angularLaurentC,masterLeading,
    masterInverse,masterInverseCube,tensorWeight,regularHDCoefficient,reducedMasterD,
    targetShift,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    field_simp
    ring


/-- The complete source-retaining master combination in each radial column. -/
def regularW (s : ℂ) (k : Fin 3) (r : ℂ) : ℂ :=
  wLeading s k*r+wInverse s k/r+wInverseCube s k/r^(3 : ℕ)

/-- The explicit regular ingoing amplitudes, ordered as vv, vr, rr and angular. -/
def regularIngoingColumn (s : ℂ) (k : Fin 3) : Fin 4 → ℝ → ℂ :=
  ![fun r => s*regularW s k r-((r:ℂ)^(2 : ℕ)-1)*tensorWeight s k*tensorCoefficient s r+
      ((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)/2*regularIngoingRR s k r,
    fun r => tensorWeight s k*tensorCoefficient s r-((r:ℂ)^(2 : ℕ)-1)/2*regularIngoingRR s k r,
    fun r => regularIngoingRR s k r,
    fun r => regularAngularColumn s k r]

/-- The ordinary tensor coordinate transformation induced by dt=dv-dr/(r²-1). -/
def ingoingTransform (F : Fin 4 → ℝ → ℂ) : Fin 4 → ℝ → ℂ :=
  ![F 0,fun r => F 1 r-F 0 r/((r:ℂ)^(2 : ℕ)-1),
    fun r => F 2 r-2*F 1 r/((r:ℂ)^(2 : ℕ)-1)+F 0 r/((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ),F 3]

private theorem radial_column_trace (s : ℂ) (k : Fin 3) (r : ℝ) :
    radialColumn s k 0 r = ((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*radialColumn s k 2 r-
      2*((r:ℂ)^(2 : ℕ)-1)*tensorWeight s k*tensorCoefficient s r := by
  fin_cases k <;> simp only [radialColumn,tensorWeight,metricF00,metricF02,metricF0D,
    Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Fin.reduceFinMk]
  all_goals ring

private theorem radial_column_mixed (s : ℂ) (hs : s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) (k : Fin 3) :
    ((r:ℂ)^(2 : ℕ)-1)*radialColumn s k 1 r = s*regularW s k r := by
  have hf := (exterior_ne r hr1).2
  have hr := (exterior_ne r hr1).1
  have h0 := angular_column_laurent s hs hshift hr1 0
  have h2 := angular_column_laurent s hs hshift hr1 1
  have hD := angular_column_laurent s hs hshift hr1 2
  simp only [radialColumn,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    at h0 h2 hD
  fin_cases k <;> simp only [radialColumn,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Fin.reduceFinMk,
    metricF12,metricF1D,h2,hD,regularW,wLeading,wInverse,wInverseCube,regularAngularColumn,
    masterLeading,masterInverse,masterInverseCube,reducedMasterD,angularLaurentA,angularLaurentB,angularLaurentC]
  all_goals field_simp
  all_goals ring

/-- Every original radial column has the explicit ingoing extension, with all source terms retained. -/
theorem original_ingoing_column (s : ℂ) (hs : s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) (k : Fin 3) (j : Fin 4) :
    ingoingTransform (radialColumn s k) j r = regularIngoingColumn s k j r := by
  have hf := (exterior_ne r hr1).2
  have hrr := original_ingoing_rr s hs hshift hr1 k
  have htrace := radial_column_trace s k r
  have hmix := radial_column_mixed s hs hshift hr1 k
  have hrr' : ((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*radialColumn s k 2 r-
      2*((r:ℂ)^(2 : ℕ)-1)*radialColumn s k 1 r+radialColumn s k 0 r =
      ((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*regularIngoingRR s k r := by
    field_simp at hrr
    linear_combination hrr
  fin_cases j <;> simp only [ingoingTransform,regularIngoingColumn,
    Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.reduceFinMk]
  · linear_combination hmix+htrace/2+hrr'/2
  · field_simp
    linear_combination -hrr'-htrace
  · exact hrr
  · exact angular_column_laurent s hs hshift hr1 k

/-- All ingoing coefficients have every derivative across the horizon. -/
theorem regularIngoingColumn_smooth (s : ℂ) (k : Fin 3) (j : Fin 4)
    {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ∞ (regularIngoingColumn s k j) r := by
  have h0 : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hp : (r:ℂ)+1 ≠ 0 := by exact_mod_cast (show r+1 ≠ 0 by linarith)
  fin_cases j <;> simp only [regularIngoingColumn,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,
    Matrix.tail_cons,Fin.reduceFinMk]
  all_goals try delta regularW regularIngoingRR regularAngularColumn tensorCoefficient
  all_goals simp only [div_eq_mul_inv,mul_inv]
  all_goals fun_prop (disch := aesop)

/-- Physical specialization requires no supplied spectral noncollision or horizon regularity. -/
theorem physical_ingoing_column (q : XiZeroCopy) (branch : Bool)
    {r : ℝ} (hr1 : 1 < r) (k : Fin 3) (j : Fin 4) :
    ingoingTransform (radialColumn (D4BMModularCore.physicalRate q branch) k) j r =
      regularIngoingColumn (D4BMModularCore.physicalRate q branch) k j r := by
  obtain ⟨hs,_,hshift⟩ := physical_shifts q branch
  exact original_ingoing_column _ hs hshift hr1 k j

end
end RHTower.D4BMThreeFieldHorizon
