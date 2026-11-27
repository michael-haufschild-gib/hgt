import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.GaussianFields
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.DateTail
import GaloisForLFunctions.HTGeometry.PauliContinuousLaboratoryReturnLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.ResponseWeights.PauliTrace

/-! # Uniform physical-date control of a frozen-basis approximation -/

open MeasureTheory ProbabilityTheory Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
noncomputable section

def base {n : ℕ} (x : FieldPair n) : Coeff n := fun i => (x i).1

/-- Every predicted energy is affine in the independent second field.
Its slopes are the local Pauli expectations of the base eigenstate. -/
theorem affine_energies {n : ℕ} (a b : ℝ) (x : FieldPair n) (j : Fin (n+2) → Bool) :
    let u : PathShell n := WithLp.toLp 2 (base x)
    let h := (isSelfAdjoint_pathHamiltonian u).isHermitian
    diagonalEnergy h.eigenvectorUnitary (generator (rotated a b x)).val j =
      a*h.eigenvalues j + b*∑ l, (x l).2*FirstGate.ResponseWeights.localMean u l j := by
  intro u h
  have hsum (v : Coeff n) : diagonalEnergy h.eigenvectorUnitary (generator v).val j =
      ∑ l, v l*FirstGate.ResponseWeights.localMean u l j := by
    change (((h.eigenvectorUnitary.val)ᴴ*pathHamiltonian (WithLp.toLp 2 v)*h.eigenvectorUnitary.val) j j).re=_
    rw [pathHamiltonian_eq_sum,Finset.mul_sum,Finset.sum_mul,Matrix.sum_apply,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro l _
    simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_apply,smul_eq_mul,Complex.re_ofReal_mul]
    rfl
  have hE : h.eigenvalues j=∑ l, (x l).1*FirstGate.ResponseWeights.localMean u l j :=
    FirstGate.energy_from_local_expectations u j
  rw [hsum,hE,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  dsimp only [rotated]
  ring

private theorem base_law (n : ℕ) : MeasurePreserving (base (n:=n)) (pairLaw n) (fieldLaw n) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_fst)

def excess {n : ℕ} (a b : ℝ) (x : FieldPair n) : ℝ :=
  spectralSpread (generator (rotated a b x))+spectralSpread (generator (rotated a (-b) x))-
    2*a*spectralSpread (generator (base x))

private theorem midpoint {n : ℕ} (a b : ℝ) (x : FieldPair n) :
    (generator (rotated a b x)).val+(generator (rotated a (-b) x)).val=
      (2*a) • (generator (base x)).val := by
  let u (v : Coeff n) : PathShell n := WithLp.toLp 2 v
  change pathHamiltonianLM n (u (rotated a b x))+pathHamiltonianLM n (u (rotated a (-b) x))=
    (2*a) • pathHamiltonianLM n (u (base x))
  rw [←map_add,←map_smul]
  apply congrArg (pathHamiltonianLM n)
  apply WithLp.ofLp_injective 2
  funext i
  change (a*(x i).1+b*(x i).2)+(a*(x i).1+ -b*(x i).2)=(2*a)*(x i).1
  ring

/-- Both fields enter with their true Gaussian marginal, including at a
degenerate base spectrum. Their excess spread has an exact mean. -/
theorem mean_excess (n : ℕ) {a b : ℝ} (hab : a^2+b^2=1) :
    Integrable (excess (n:=n) a b) (pairLaw n) ∧
    (∫ x, excess a b x ∂pairLaw n)=
      2*(1-a)*(∫ y : Coeff n, spectralSpread (generator y) ∂fieldLaw n) := by
  let s (y : Coeff n) := spectralSpread (generator y)
  have hi : Integrable s (fieldLaw n) := (gaussian_spread_moment n).1
  have law (f : FieldPair n → Coeff n) (hp : MeasurePreserving f (pairLaw n) (fieldLaw n)) :
      Integrable (fun x => s (f x)) (pairLaw n) ∧
      (∫ x, s (f x) ∂pairLaw n)=∫ y, s y ∂fieldLaw n := by
    refine ⟨hp.integrable_comp_of_integrable hi,?_⟩
    have hs : AEStronglyMeasurable s (Measure.map f (pairLaw n)) := by
      rw [hp.map_eq]
      exact hi.aestronglyMeasurable
    exact (integral_map hp.measurable.aemeasurable hs).symm.trans (by rw [hp.map_eq])
  obtain ⟨ip,ep⟩ := law _ (rotated_law n hab)
  obtain ⟨im,em⟩ := law _ (rotated_law n (a:=a) (b:=-b) (by simpa only [neg_sq] using hab))
  obtain ⟨ib,eb⟩ := law _ (base_law n)
  refine ⟨(ip.add im).sub (ib.const_mul (2*a)),?_⟩
  change (∫ x, (s (rotated a b x)+s (rotated a (-b) x))-2*a*s (base x) ∂pairLaw n)=_
  rw [integral_sub (ip.add im) (ib.const_mul (2*a)),integral_add ip im,integral_const_mul,ep,em,eb]
  dsimp only [s]
  ring

def pairedError {n : ℕ} (a b : ℝ) (x : FieldPair n) (t : ℝ) :=
  predictionError (generator (base x)) (generator (rotated a b x)) t+
    predictionError (generator (base x)) (generator (rotated a (-b) x)) t

private theorem time_bound {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (x : FieldPair n) (t : ℝ) :
    pairedError a b x t ≤ 2*|t| *excess a b x :=
  paired_prediction_error _ _ _ ha (midpoint a b x) t

private theorem excess_nonneg {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (x : FieldPair n) :
    0 ≤ excess a b x := by
  have h := time_bound ha b x 1
  have hpos : 0 ≤ pairedError a b x 1 := add_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _)
  rw [abs_one,mul_one] at h
  linarith only [h,hpos]

/-- The same exceptional set controls both signs at every date in the
horizon, even when the observation date depends on the sample. -/
theorem gaussian_uniform_prediction (n : ℕ) {a b T ρ : ℝ}
    (ha : 0 ≤ a) (hab : a^2+b^2=1) (hT : 0<T) (hρ : 0<ρ) :
    (pairLaw n).real {x | ∃ t : ℝ, |t| ≤ T ∧ (2:ℝ)^(n+2)*ρ^2 < pairedError a b x t} ≤ 8*T*(1-a)*(2:ℝ)^(n+2)*Real.sqrt (Fintype.card (PathLabel n))/ρ^2 := by
  let D := (2:ℝ)^(n+2)
  let κ := D*ρ^2/(2*T)
  have hD : 0<D := by dsimp [D]; positivity
  have hκ : 0<κ := div_pos (mul_pos hD (sq_pos_of_pos hρ)) (mul_pos (by norm_num) hT)
  have ha₁ : 0 ≤ 1-a := by nlinarith only [hab,sq_nonneg b,sq_nonneg (a-1)]
  have hpos : 0 ≤ᵐ[pairLaw n] excess a b := ae_of_all _ fun x => excess_nonneg ha b x
  obtain ⟨hi,hm⟩ := mean_excess n hab
  have hmark := mul_meas_ge_le_integral_of_nonneg hpos hi κ
  have hu := mul_le_mul_of_nonneg_left (gaussian_spread_moment n).2 (mul_nonneg (by norm_num) ha₁)
  rw [hm] at hmark
  apply (measureReal_mono (μ:=pairLaw n) (s₂:={x | κ ≤ excess a b x}) ?_).trans
  · apply (le_of_mul_le_mul_left · hκ)
    apply (hmark.trans hu).trans_eq
    dsimp only [κ,D]
    field_simp
    <;> ring
  · rintro x ⟨t,ht,herr⟩
    apply (div_le_iff₀ (mul_pos (by norm_num) hT)).mpr
    have h := (time_bound ha b x t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht (by norm_num)) (excess_nonneg ha b x))
    exact (herr.le.trans h).trans_eq (mul_comm ..)

/-- A circuit fitting the actual propagator also fits its diagonal phase
prediction in normalized Frobenius distance on the good event. -/
theorem circuit_prediction {n : ℕ} (a b : ℝ) (x : FieldPair n) (t ε ρ : ℝ) (hρ : 0 ≤ ρ)
    (hgood : pairedError a b x t ≤ (2:ℝ)^(n+2)*ρ^2) :
    ∀ (c : ℂ) (C : TwoQubitCircuit (n+2)),
    ‖unitaryEvolution (generator (rotated a b x)).val t-c • C.eval.val‖ ≤ ε →
    hsNorm (diagonalPrediction (generator (base x)).2.isHermitian.eigenvectorUnitary
      (generator (rotated a b x)).val t-c • C.eval.val) ≤ Real.sqrt ((2:ℝ)^(n+2))*(ε+ρ) := by
  intro c C herr
  let V := diagonalPrediction (generator (base x)).2.isHermitian.eigenvectorUnitary
    (generator (rotated a b x)).val t
  let U := unitaryEvolution (generator (rotated a b x)).val t
  let W := c • C.eval.val
  let D := (2:ℝ)^(n+2)
  have hpred : hsNorm (V-U) ≤ Real.sqrt D*ρ := by
    apply (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hρ)).mp
    rw [hsNorm_sq,mul_pow,Real.sq_sqrt (by dsimp only [D]; positivity)]
    have hs : (∑ i, ∑ j, ‖(V-U) i j‖^2)=hsNormSq (U-V) := by
      rw [hsNormSq,Finset.sum_comm]
      simp only [Matrix.sub_apply,norm_sub_rev (V _ _) (U _ _)]
    rw [hs]
    exact (le_add_of_nonneg_right (hsNormSq_nonneg _)).trans hgood
  have hc := hsNorm_le_sqrt_card_mul_opNorm (U-W)
  have hd : (Fintype.card (Fin (n+2) → Bool):ℝ)=D := by simp [D]
  rw [hd] at hc
  apply (hsNorm_sub_le V U W).trans
  exact (add_le_add hpred (hc.trans (mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg _)))).trans_eq (by ring)

/-- Draws on which the affine diagonal phases fit a circuit of the specified
budget and normalized Frobenius tolerance. -/
def diagonalFit (n s : ℕ) (a b t η : ℝ) : Set (FieldPair n) :=
  {x | ∃ c : ℂ, ‖c‖=1 ∧ ∃ C : TwoQubitCircuit (n+2), C.gateCount ≤ s ∧
    hsNorm (diagonalPrediction (generator (base x)).2.isHermitian.eigenvectorUnitary
      (generator (rotated a b x)).val t-c • C.eval.val) ≤ Real.sqrt ((2:ℝ)^(n+2))*η}

/-- At every prescribed date and every gate budget, the original physical
shortcut probability is bounded by affine-phase capture plus a field error. -/
theorem gaussian_date_circuit_comparison (n s : ℕ) {a b T ρ : ℝ} (ha : 0 ≤ a)
    (hab : a^2+b^2=1) (hT : 0<T) (hρ : 0<ρ) (t ε : ℝ) (ht : |t| ≤ T) :
    pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹'
      BlockDilations.affordableDraw n s ε t) ≤ (pairLaw n).real (diagonalFit n s a b t (ε+ρ))+
        8*T*(1-a)*(2:ℝ)^(n+2)*Real.sqrt (Fintype.card (PathLabel n))/ρ^2 := by
  let A := BlockDilations.affordableDraw n s ε t
  let bad : Set (FieldPair n) := {x | ∃ u : ℝ, |u| ≤ T ∧ (2:ℝ)^(n+2)*ρ^2<pairedError a b x u}
  have hm : MeasurableSet A := BlockDilations.measurable_affordableDraw ..
  have he : pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹' A)=
      (pairLaw n).real (rotated a b ⁻¹' A) := by
    unfold Measure.real
    rw [(BlockDilations.prefix_measure n).measure_preimage hm.nullMeasurableSet,
      (rotated_law n hab).measure_preimage hm.nullMeasurableSet]
  rw [he]
  have hs : rotated a b ⁻¹' A ⊆ diagonalFit n s a b t (ε+ρ) ∪ bad := by
    rintro x ⟨c,hc,C,hsize,herr⟩
    by_cases h : (2:ℝ)^(n+2)*ρ^2<pairedError a b x t
    · exact Or.inr ⟨t,ht,h⟩
    · exact Or.inl ⟨c,hc,C,hsize,circuit_prediction a b x t ε ρ hρ.le (le_of_not_gt h) c C herr⟩
  exact (measureReal_mono hs).trans ((measureReal_union_le ..).trans
    (add_le_add_left (gaussian_uniform_prediction n ha hab hT hρ) _))

/-- An independent phase shift of size L at time T costs at most
8 D √m L²/(T ρ²) in physical shortcut probability. -/
theorem physical_phase_scale (n s : ℕ) {T L ρ : ℝ} (hT : 0<T) (hL : |L| ≤ T) (hρ : 0<ρ) (ε : ℝ) :
    let b := L/T
    let a := Real.sqrt (1-b^2)
    pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹'
      BlockDilations.affordableDraw n s ε T) ≤ (pairLaw n).real (diagonalFit n s a b T (ε+ρ))+
        8*(2:ℝ)^(n+2)*Real.sqrt (Fintype.card (PathLabel n))*L^2/(T*ρ^2) := by
  intro b a
  have hb : |b| ≤ 1 := by
    dsimp only [b]
    rw [abs_div,abs_of_pos hT]
    exact (div_le_one hT).mpr hL
  have hb₂ : b^2 ≤ 1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hab : a^2+b^2=1 := by rw [Real.sq_sqrt (sub_nonneg.mpr hb₂)]; ring
  have ha₁ : a ≤ 1 := by nlinarith only [hab,sq_nonneg b,sq_nonneg (a-1)]
  have hloss : 1-a ≤ b^2 := by nlinarith only [hab,mul_nonneg ha (sub_nonneg.mpr ha₁)]
  apply (gaussian_date_circuit_comparison n s ha hab hT hρ T ε (abs_of_pos hT).le).trans
  apply add_le_add_left
  calc
    _ ≤ 8*T*b^2*(2:ℝ)^(n+2)*Real.sqrt (Fintype.card (PathLabel n))/ρ^2 := by
      gcongr
    _ = _ := by dsimp only [b]; field_simp; ring

#print axioms physical_phase_scale
#print axioms gaussian_date_circuit_comparison
#print axioms mean_excess
#print axioms gaussian_uniform_prediction
#print axioms circuit_prediction
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
