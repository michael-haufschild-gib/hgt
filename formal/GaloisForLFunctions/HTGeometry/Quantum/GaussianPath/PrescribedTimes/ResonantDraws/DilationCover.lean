import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation

/-! # A Gaussian mass floor from a covering by contracted samples -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
noncomputable section

/-- A contracted copy of a Gaussian vector pays at most the inverse
Jacobian. A set covered by finitely many such preimages has mass at
most the target probability times the sum of the inverse Jacobians. -/
theorem dilation_cover_mass_on {ι I : Type*} [Fintype ι] [Fintype I]
    (K E : Set (ι → ℝ)) (hE : MeasurableSet E) (b : I → ℝ) (hb : ∀ i, 1 ≤ b i)
    (hcover : ∀ x ∈ K, ∃ i, (b i)⁻¹ • x ∈ E) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    μ.real K ≤ (∑ i, (b i)^Fintype.card ι)*μ.real E := by
  intro μ
  let S (i : I) := (fun x : ι → ℝ => (b i)⁻¹ • x) ⁻¹' E
  have hS (i : I) : MeasurableSet (S i) :=
    hE.preimage (measurable_id' (α := ι → ℝ) |>.const_smul ((b i)⁻¹))
  have he (i : I) : (fun x : ι → ℝ => b i • x) ⁻¹' S i = E := by
    ext x
    change (b i)⁻¹ • b i • x ∈ E ↔ x ∈ E
    rw [smul_smul,inv_mul_cancel₀ (zero_lt_one.trans_le (hb i)).ne',one_smul]
  have hp (i : I) : μ.real (S i) ≤ (b i)^Fintype.card ι*μ.real E := by
    simpa only [he i] using gaussian_dilation_comparison (hb i) (S i) (hS i)
  have hu : K ⊆ ⋃ i, S i := fun x hx => mem_iUnion.mpr (hcover x hx)
  calc
    μ.real K ≤ μ.real (⋃ i, S i) := measureReal_mono hu
    _ ≤ ∑ i, μ.real (S i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, (b i)^Fintype.card ι*μ.real E := Finset.sum_le_sum fun i _ => hp i
    _ = _ := (Finset.sum_mul ..).symm

/-- When the contractions cover the whole coefficient space, the
target has a positive probability floor independent of the date. -/
theorem dilation_cover_mass {ι I : Type*} [Fintype ι] [Fintype I]
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) (b : I → ℝ) (hb : ∀ i, 1 ≤ b i)
    (hcover : ∀ x : ι → ℝ, ∃ i, (b i)⁻¹ • x ∈ E) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    1 ≤ (∑ i, (b i)^Fintype.card ι)*μ.real E := by
  simpa only [probReal_univ] using dilation_cover_mass_on univ E hE b hb (fun x _ => hcover x)

/-- On the positive M-point rational grid, the Gaussian price of
covering a starting set is bounded by M to the dimension plus one. -/
theorem rational_grid_price {ι : Type*} [Fintype ι] (M : ℕ) (K E : Set (ι → ℝ))
    (hE : MeasurableSet E) (hits : ∀ x ∈ K, ∃ q : ℕ, 1 ≤ q ∧ q ≤ M ∧ ((q:ℝ)/M) • x ∈ E) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    μ.real K ≤ (M:ℝ)^(Fintype.card ι+1)*μ.real E := by
  intro μ
  let b (i : Fin M) := (M:ℝ)/((i.val:ℝ)+1)
  have hb (i : Fin M) : 1 ≤ b i := (one_le_div (by positivity)).mpr (by exact_mod_cast Nat.succ_le_of_lt i.isLt)
  have hc (x : ι → ℝ) (hx : x∈K) : ∃ i, (b i)⁻¹ • x ∈ E := by
    obtain ⟨q,hq,hqM,hfit⟩ := hits x hx
    let i : Fin M := ⟨q-1,by omega⟩
    have hi : (i.val:ℝ)+1=q := by exact_mod_cast (Nat.sub_add_cancel hq : i.val+1=q)
    refine ⟨i,?_⟩
    change ((M:ℝ)/((i.val:ℝ)+1))⁻¹ • x ∈ E
    rwa [hi,inv_div]
  have hp (i : Fin M) : b i ≤ (M:ℝ) :=
    div_le_self (Nat.cast_nonneg M) (le_add_of_nonneg_left (Nat.cast_nonneg i.val))
  have hs : (∑ i, (b i)^Fintype.card ι) ≤ (M:ℝ)^(Fintype.card ι+1) := calc
    _ ≤ ∑ _ : Fin M, (M:ℝ)^Fintype.card ι := Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (zero_le_one.trans (hb i)) (hp i) _
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,pow_succ']
  exact (dilation_cover_mass_on K E hE b hb hc).trans (mul_le_mul_of_nonneg_right hs measureReal_nonneg)

#print axioms dilation_cover_mass
#print axioms rational_grid_price
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
