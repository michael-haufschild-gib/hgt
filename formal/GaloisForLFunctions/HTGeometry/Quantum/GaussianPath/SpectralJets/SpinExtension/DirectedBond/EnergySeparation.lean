import GaloisForLFunctions.HTGeometry.PolynomialMatrixSimpleSpectrumTransport
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Separation of finite energy levels in two distant spin sectors -/
open Filter Topology Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I : Type*} [Fintype I]

def height (n : ℕ) : ℂ := n+1
def inverseHeight (n : ℕ) : ℂ := 1/height n

theorem height_ne_zero (n : ℕ) : height n≠0 := by
  change (n:ℂ)+1≠0
  exact_mod_cast Nat.succ_ne_zero n

theorem height_mul_inverse (n : ℕ) : height n*inverseHeight n=1 :=
  mul_one_div_cancel (height_ne_zero n)

theorem inverseHeight_tendsto : Tendsto inverseHeight atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem eventually_separate {f g : ℕ→ℂ} {a b : ℂ}
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) (hab : a≠b) :
    ∀ᶠ n in atTop, f n≠g n := by
  have h := (hf.sub hg).eventually (isOpen_ne.mem_nhds (sub_ne_zero.mpr hab))
  exact h.mono fun n hn => sub_ne_zero.mp hn

/-- Distinct old levels remain distinct within each spin sector. Multiplying
the energies by the inverse splitting separates opposite sectors. -/
theorem separated_sectors (E₀ : I→ℂ) (hI : Function.Injective E₀) (p q : I→ℕ→ℂ)
    (hp : ∀ i, Tendsto (p i) atTop (𝓝 (E₀ i))) (hq : ∀ i, Tendsto (q i) atTop (𝓝 (E₀ i))) :
    ∀ᶠ n : ℕ in atTop, Function.Injective (Sum.elim (fun i => height n+p i n) (fun i => -height n+q i n)) := by
  have hscaled (s : ℂ) (f : ℕ→ℂ) {a : ℂ} (hf : Tendsto f atTop (𝓝 a)) :
      Tendsto (fun n => inverseHeight n*(s*height n+f n)) atTop (𝓝 s) := by
    have he (n : ℕ) : inverseHeight n*(s*height n+f n)=s+inverseHeight n*f n := by
      rw [mul_add,show inverseHeight n*(s*height n)=s*(height n*inverseHeight n) by ring,height_mul_inverse,mul_one]
    simp only [he]
    simpa only [zero_mul,add_zero] using tendsto_const_nhds.add (inverseHeight_tendsto.mul hf)
  have hcross (i j : I) : ∀ᶠ n in atTop, height n+p i n≠-height n+q j n := by
    have h := eventually_separate (hscaled 1 _ (hp i)) (hscaled (-1) _ (hq j)) (by norm_num)
    filter_upwards [h] with n hn he
    exact hn (by simp only [one_mul,neg_one_mul,he])
  have hin (r : I→ℕ→ℂ) (hr : ∀ i, Tendsto (r i) atTop (𝓝 (E₀ i))) :
      ∀ᶠ n in atTop, Function.Injective (fun i => r i n) := by
    have hh (i j : I) : ∀ᶠ n in atTop, r i n=r j n → i=j := by
      by_cases he : i=j
      · exact Eventually.of_forall fun _ _ => he
      · exact (eventually_separate (hr i) (hr j) (hI.ne he)).mono fun _ h hr' => (h hr').elim
    exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hh i j
  filter_upwards [hin p hp,hin q hq,Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hcross i)] with n h₁ h₂ h₃
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (h₁ (add_left_cancel h))
    | inr j => exact (h₃ i j h).elim
  | inr i =>
    cases j with
    | inl j => exact (h₃ j i h.symm).elim
    | inr j => exact congrArg Sum.inr (h₂ (add_left_cancel h))

/-- A complete family of distinct energies consists of simple characteristic roots. -/
theorem simple_packet [DecidableEq I] (H : Matrix I I ℂ) (e : I→ℂ) (he : Function.Injective e)
    (hr : ∀ i, H.charpoly.eval (e i)=0) (i : I) : H.charpoly.derivative.eval (e i)≠0 := by
  have hres : Polynomial.resultant H.charpoly H.charpoly.derivative≠0 := by
    simpa [H.charpoly_natDegree_eq_dim,Polynomial.natDegree_derivative] using
      matrixCharacteristicResultant_ne_zero_of_complete_injective_roots H e he hr
  intro hd
  apply hres
  refine Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl H.charpoly_monic.ne_zero,?_⟩
  rintro ⟨u,v,h⟩
  have hh := congrArg (Polynomial.eval (e i)) h
  exact zero_ne_one (by simpa only [eval_add,eval_mul,hr,hd,mul_zero,zero_add,eval_one] using hh)

#print axioms separated_sectors
#print axioms simple_packet
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
