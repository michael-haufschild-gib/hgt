import GaloisForLFunctions.HTGeometry.ClockResponseIdentifiability

/-!
# Quantified stability of a clock response

Identifiability says that complete probe data determine the response operator. A laboratory
measures the data only approximately, so what the reconstruction really needs is a bound: a response
consistent with the data to within `ε` is close to the true response in operator norm.

That bound holds as soon as the two families are *norming* — the readouts control the norm of a
response, and the drives control the norm of an operator — and both requirements are met by the
canonical families, the dual unit ball and the unit ball, with constant `1`. Behind unknown endpoint
gains the same estimate survives, with the reciprocal of a lower bound for the receiver and the norm
of a right inverse of the source as the amplification factors.
-/

namespace GaloisForLFunctions.HTGeometry

section Norming

variable {𝕜 : Type*} [RCLike 𝕜]
variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {ι ι' : Type*}

/-- Readouts norm responses with constant `C`: a response whose readings are all at most `ε` has
norm at most `C ε`. -/
def NormingReadouts (C : ℝ) (readout : ι → F →L[𝕜] 𝕜) : Prop :=
  ∀ (y : F) (ε : ℝ), (∀ i, ‖readout i y‖ ≤ ε) → ‖y‖ ≤ C * ε

/-- Drives norm operators with constant `C`: an operator whose responses to all drives are at most
`ε` has operator norm at most `C ε`. -/
def NormingDrives (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (C : ℝ) (drive : ι' → E) :
    Prop :=
  ∀ (L : E →L[𝕜] F) (ε : ℝ), 0 ≤ ε → (∀ j, ‖L (drive j)‖ ≤ ε) → ‖L‖ ≤ C * ε

/-- **The dual unit ball is norming with constant `1`.** -/
theorem normingReadouts_dualBall :
    NormingReadouts (F := F) (𝕜 := 𝕜) 1
      (fun φ : {φ : F →L[𝕜] 𝕜 // ‖φ‖ ≤ 1} => (φ : F →L[𝕜] 𝕜)) := by
  intro y ε hy
  obtain ⟨g, hgnorm, hg⟩ := exists_dual_vector'' 𝕜 y
  have hval := hy ⟨g, hgnorm⟩
  rw [hg] at hval
  rw [one_mul]
  simpa using hval

/-- **The unit ball is norming with constant `1`.** -/
theorem normingDrives_unitBall :
    NormingDrives (𝕜 := 𝕜) F 1 (fun x : {x : E // ‖x‖ ≤ 1} => (x : E)) := by
  intro L ε hε hL
  rw [one_mul]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hε ?_
  intro x hx
  exact hL ⟨x, le_of_eq hx⟩

/-! ## The stability estimate -/

/-- **Quantified stability of the measured response.** Two response operators whose data agree to
within `ε` differ by at most `C_drive C_readout ε` in operator norm. -/
theorem responseOperator_norm_sub_le_of_data {T S : E →L[𝕜] F} {drive : ι' → E}
    {readout : ι → F →L[𝕜] 𝕜} {Cd Cr ε : ℝ} (hε : 0 ≤ ε) (hCr : 0 ≤ Cr)
    (hdrive : NormingDrives (𝕜 := 𝕜) F Cd drive) (hread : NormingReadouts Cr readout)
    (hdata : ∀ (i : ι) (j : ι'),
      ‖readout i (T (drive j)) - readout i (S (drive j))‖ ≤ ε) :
    ‖T - S‖ ≤ Cd * (Cr * ε) := by
  refine hdrive (T - S) (Cr * ε) (mul_nonneg hCr hε) fun j => ?_
  refine hread ((T - S) (drive j)) ε fun i => ?_
  rw [sub_apply, map_sub]
  exact hdata i j

/-- A receiver bounded below and a bounded right inverse of the source convert a bound on the
dressed operator into a bound on the undressed one. -/
theorem norm_le_of_dressed_norm (receiver : F →L[𝕜] G) (source : D →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ y : F, c * ‖y‖ ≤ ‖receiver y‖)
    (right : E →L[𝕜] D) (hright : ∀ x : E, source (right x) = x) (L : E →L[𝕜] F) :
    ‖L‖ ≤ c⁻¹ * ‖right‖ * ‖receiver.comp (L.comp source)‖ := by
  have hnonneg : (0 : ℝ) ≤ c⁻¹ * ‖right‖ * ‖receiver.comp (L.comp source)‖ :=
    mul_nonneg (mul_nonneg (inv_pos.mpr hc).le (norm_nonneg _)) (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hnonneg fun x => ?_
  have hdressed : ‖receiver (L x)‖ ≤ ‖receiver.comp (L.comp source)‖ * (‖right‖ * ‖x‖) := by
    have hx : receiver (L x) = (receiver.comp (L.comp source)) (right x) := by
      show receiver (L x) = receiver (L (source (right x)))
      rw [hright x]
    rw [hx]
    refine ((receiver.comp (L.comp source)).le_opNorm (right x)).trans ?_
    exact mul_le_mul_of_nonneg_left (right.le_opNorm x) (norm_nonneg _)
  have hbase : c * ‖L x‖ ≤ ‖receiver.comp (L.comp source)‖ * (‖right‖ * ‖x‖) :=
    (hlower (L x)).trans hdressed
  have hle : ‖L x‖ ≤ ‖receiver.comp (L.comp source)‖ * (‖right‖ * ‖x‖) / c := by
    rw [le_div_iff₀ hc, mul_comm]
    exact hbase
  refine hle.trans_eq ?_
  field_simp

/-- **Quantified stability of the hidden response.** With norming drives and readouts, a receiver
bounded below and a bounded right inverse of the source, two hidden responses whose measured data
agree to within `ε` differ by at most `c⁻¹‖right‖ C_drive C_readout ε`. -/
theorem hiddenResponse_norm_sub_le_of_data {T S : E →L[𝕜] F} (receiver : F →L[𝕜] G)
    (source : D →L[𝕜] E) {c : ℝ} (hc : 0 < c) (hlower : ∀ y : F, c * ‖y‖ ≤ ‖receiver y‖)
    (right : E →L[𝕜] D) (hright : ∀ x : E, source (right x) = x)
    {drive : ι' → D} {readout : ι → G →L[𝕜] 𝕜} {Cd Cr ε : ℝ} (hε : 0 ≤ ε) (hCr : 0 ≤ Cr)
    (hdrive : NormingDrives (𝕜 := 𝕜) G Cd drive) (hread : NormingReadouts Cr readout)
    (hdata : ∀ (i : ι) (j : ι'),
      ‖readout i (receiver (T (source (drive j)))) -
        readout i (receiver (S (source (drive j))))‖ ≤ ε) :
    ‖T - S‖ ≤ c⁻¹ * ‖right‖ * (Cd * (Cr * ε)) := by
  have hsplit : receiver.comp ((T - S).comp source) =
      receiver.comp (T.comp source) - receiver.comp (S.comp source) := by
    ext v
    simp
  have hmeasured : ‖receiver.comp (T.comp source) - receiver.comp (S.comp source)‖
      ≤ Cd * (Cr * ε) :=
    responseOperator_norm_sub_le_of_data hε hCr hdrive hread hdata
  have hbase := norm_le_of_dressed_norm receiver source hc hlower right hright (T - S)
  rw [hsplit] at hbase
  refine hbase.trans ?_
  exact mul_le_mul_of_nonneg_left hmeasured
    (mul_nonneg (inv_pos.mpr hc).le (norm_nonneg _))

end Norming

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.hiddenResponse_norm_sub_le_of_data
#print axioms GaloisForLFunctions.HTGeometry.normingDrives_unitBall
#print axioms GaloisForLFunctions.HTGeometry.normingReadouts_dualBall
