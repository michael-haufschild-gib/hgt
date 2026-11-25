import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.ActionGerms
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.LineBranches
import GaloisForLFunctions.HTGeometry.SortedSpectrumGapExtremality

/-! # Local algebraic continuations of normalized spectral actions -/

open Set Filter Matrix Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

/-- The action of a spectral weight measured in units of a selected gap. -/
def normalizedAction {I : Type*} [Fintype I] (w E : I → ℝ) (i j : I) : ℝ :=
  (∑ l, w l*E l)/(E i-E j)

/-- Over a segment of simple spectra, the normalized actions have
algebraic complex germs at the first endpoint. Distinct changes along
the segment force their pairwise differences to be nonconstant. -/
theorem line_actions {n D : ℕ} {P : Fin n → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ l, (P l).IsHermitian) (x y : Fin n → ℝ) (i j : Fin D) (hij : i≠j)
    {L : Type*} [Fintype L] (w : L → Fin D → ℝ) {χ : ℂ} (hχ : χ≠0)
    (hseg : ∀ t ∈ Icc (0:ℝ) 1, x+t • (y-x)∈simpleEnsembleLocus hP)
    (hd : ∀ u v, u≠v →
      normalizedAction (w u) (sortedEnsembleSpectrum hP x) i j -
        normalizedAction (w v) (sortedEnsembleSpectrum hP x) i j ≠
      normalizedAction (w u) (sortedEnsembleSpectrum hP y) i j -
        normalizedAction (w v) (sortedEnsembleSpectrum hP y) i j) :
    ∃ f : L → ℂ → ℂ, ∃ hf : ∀ u, AnalyticAt ℂ (f u) 0,
      (∀ u, IsAlgebraic (RatFunc ℂ) (ofMero (f u) (hf u).meromorphicAt)) ∧
      (∀ᶠ t : ℝ in 𝓝 0, ∀ u, f u t =
        χ*(normalizedAction (w u) (sortedEnsembleSpectrum hP (x+t • (y-x))) i j : ℝ)) ∧
      ∀ u v, u≠v → ∀ c : ℂ, ¬((fun z => f u z-f v z) =ᶠ[𝓝[≠] 0] fun _ => c) := by
  let line (t : ℝ) := x+t • (y-x)
  let E := sortedEnsembleSpectrum hP
  have h0 : line 0=x := by simp [line]
  have h1 : line 1=y := by simp [line]
  have hx : x∈simpleEnsembleLocus hP := by
    simpa only [zero_smul,add_zero] using hseg 0 (left_mem_Icc.mpr zero_le_one)
  choose g hg hag hreal using line_energy_germ hP x (y-x) hx
  have hr : ∀ᶠ t : ℝ in 𝓝 0, ∀ l, g l t = (E (line t) l:ℂ) :=
    Filter.eventually_all.mpr hreal
  have hvalue (l : Fin D) : g l 0=(E x l:ℂ) := by
    simpa only [Complex.ofReal_zero,h0] using hr.self_of_nhds l
  have hgap : g i 0-g j 0≠0 := by
    rw [hvalue,hvalue]
    exact sub_ne_zero.mpr (Complex.ofReal_injective.ne ((injective_sortedEnsembleSpectrum hP hx).ne hij))
  let c (u : L) (l : Fin D) := χ*(w u l:ℂ)
  let f (u : L) (z : ℂ) := (∑ l, c u l*g l z)*(g i z-g j z)⁻¹
  have hf (u : L) : AnalyticAt ℂ (f u) 0 :=
    (Finset.analyticAt_fun_sum _ fun l _ => analyticAt_const.mul (hg l)).mul (((hg i).sub (hg j)).inv hgap)
  let F (u : L) (t : ℝ) := χ*(normalizedAction (w u) (E (line t)) i j : ℝ)
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ u, f u t=F u t := by
    filter_upwards [hr] with t ht u
    simp only [f,F,normalizedAction,c,ht,Complex.ofReal_div,Complex.ofReal_sum,
      Complex.ofReal_mul,Complex.ofReal_sub]
    simp only [div_eq_mul_inv,mul_assoc,←Finset.mul_sum]
  refine ⟨f,hf,fun u => ratio_germ_algebraic g (fun l => (hg l).meromorphicAt) hag
    (c u) i j (hf u).meromorphicAt,he,?_⟩
  intro u v huv c₀
  have hL (t : ℝ) : AnalyticAt ℝ line t := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hF (u : L) : AnalyticOnNhd ℝ (F u) (Icc 0 1) := by
    intro t ht
    have hE (l : Fin D) : AnalyticAt ℝ (fun v => E (line v) l) t :=
      AnalyticAt.comp (f:=line) (analyticAt_sortedEnsembleSpectrum hP (hseg t ht) l) (hL t)
    have hd' := sub_ne_zero.mpr ((injective_sortedEnsembleSpectrum hP (hseg t ht)).ne hij)
    have ha : AnalyticAt ℝ (fun t => normalizedAction (w u) (E (line t)) i j) t :=
      (Finset.analyticAt_fun_sum _ fun l _ => analyticAt_const.mul (hE l)).div ((hE i).sub (hE j)) hd'
    exact analyticAt_const.mul ((Complex.ofRealCLM.analyticAt _).comp ha)
  have hdiff (t : ℝ) : F u t-F v t=χ*((normalizedAction (w u) (E (line t)) i j-
      normalizedAction (w v) (E (line t)) i j:ℝ):ℂ) := by
    simp only [F,Complex.ofReal_sub,mul_sub]
  have hend : F u 0-F v 0≠F u 1-F v 1 := by
    intro hz
    rw [hdiff,hdiff,h0,h1] at hz
    exact hd u v huv (Complex.ofReal_injective (mul_left_cancel₀ hχ hz))
  exact nonconstant_of_segment (F:=fun t => F u t-F v t) ((hf u).sub (hf v)) ((hF u).sub (hF v))
    (he.mono fun _ ht => congrArg₂ (·-·) (ht u) (ht v)) hend c₀

#print axioms line_actions
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
