import GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles
import GaloisForLFunctions.RHTower.SelbergClass.AffineGammaResidues
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- The concrete one-variable Barnes integrand used in the Kaczorowski--Perelli
Gamma-contour calculation. -/
def barnesJ (ξ η : ℂ) (w : ℂ) : ℂ :=
  Gamma (ξ - w) * Gamma w * η ^ (-w)

/-- The left corner of the finite Barnes rectangle.  Its half-integral real
part separates every negative-integer Gamma pole from the boundary. -/
def barnesLeftCorner (m : ℕ) (T : ℝ) : ℂ :=
  (-((m : ℝ) + 1 / 2) : ℂ) - (T : ℂ) * I

/-- The right corner of the finite Barnes rectangle. -/
def barnesRightCorner (c T : ℝ) : ℂ :=
  (c : ℂ) + (T : ℂ) * I

/-- The negative-integer Gamma poles selected by the finite Barnes rectangle. -/
def barnesPoleFinset (m : ℕ) : Finset ℂ :=
  (Finset.range (m + 1)).image (fun n : ℕ => -(n : ℂ))

private theorem analyticAt_barnesCpow (η w : ℂ) (hη : η ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => η ^ (-z)) w := by
  have hdiff : Differentiable ℂ (fun z : ℂ => η ^ (-z)) :=
    Differentiable.const_cpow differentiable_neg (Or.inl hη)
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff) w (Set.mem_univ _)

private theorem analyticAt_barnesGammaLeft
    {ξ : ℂ} {c : ℝ} (hcξ : c < ξ.re) {w : ℂ} (hw : w.re ≤ c) :
    AnalyticAt ℂ (fun z : ℂ => Gamma (ξ - z)) w := by
  have hpos : 0 < (ξ - w).re := by
    simp only [sub_re]
    linarith
  have hcomp := (HTGeometry.analyticAt_Gamma_of_re_pos hpos).comp
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => ξ - z) w)
  simpa [Function.comp_def] using hcomp

private theorem meromorphicOrderAt_eq_zero_of_analytic_ne
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hz : f z ≠ 0) :
    meromorphicOrderAt f z = 0 := by
  rw [hf.meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (Or.inr hz)]
  simp

private theorem meromorphicOrderAt_barnesJ_eq_Gamma {ξ η : ℂ} {c : ℝ}
    (hcξ : c < ξ.re) (hη : η ≠ 0) {w : ℂ}
    (hw : w.re ≤ c) :
    meromorphicOrderAt (barnesJ ξ η) w = meromorphicOrderAt Gamma w := by
  have hleft : AnalyticAt ℂ (fun z : ℂ => Gamma (ξ - z)) w :=
    analyticAt_barnesGammaLeft hcξ hw
  have hleft_ne : Gamma (ξ - w) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      have hpos : 0 < (ξ - w).re := by
        simp only [sub_re]
        linarith
      exact hpos)
  have hpow : AnalyticAt ℂ (fun z : ℂ => η ^ (-z)) w :=
    analyticAt_barnesCpow η w hη
  have hpow_ne : η ^ (-w) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hη)
  have hleft_order : meromorphicOrderAt (fun z : ℂ => Gamma (ξ - z)) w = 0 :=
    meromorphicOrderAt_eq_zero_of_analytic_ne hleft hleft_ne
  have hpow_order : meromorphicOrderAt (fun z : ℂ => η ^ (-z)) w = 0 :=
    meromorphicOrderAt_eq_zero_of_analytic_ne hpow hpow_ne
  have hleft_mero : MeromorphicAt (fun z : ℂ => Gamma (ξ - z)) w := hleft.meromorphicAt
  have hpow_mero : MeromorphicAt (fun z : ℂ => η ^ (-z)) w := hpow.meromorphicAt
  have hgamma : MeromorphicAt Gamma w := Meromorphic.Gamma w
  change meromorphicOrderAt
    ((fun z : ℂ => Gamma (ξ - z)) * Gamma * (fun z : ℂ => η ^ (-z))) w = _
  rw [meromorphicOrderAt_mul (hleft_mero.mul hgamma) hpow_mero,
    meromorphicOrderAt_mul hleft_mero hgamma, hleft_order, hpow_order]
  simp

/-- Exact residue of the concrete Barnes integrand at its `n`th negative-Gamma
pole.  This is the finite-residue input for a Barnes rectangle calculation. -/
theorem residue_barnesJ_neg_nat {ξ η : ℂ}
    (hξ : 0 < ξ.re) (hη : η ≠ 0) (n : ℕ) :
    residue (barnesJ ξ η) (-(n : ℂ)) =
      ((-1 : ℂ) ^ n / (n.factorial : ℂ)) * Gamma (ξ + n) * η ^ n := by
  let p : ℂ := -(n : ℂ)
  have hleft_pos : 0 < (ξ - p).re := by
    dsimp [p]
    simpa using (add_pos_of_pos_of_nonneg hξ (Nat.cast_nonneg n))
  have hleft : AnalyticAt ℂ (fun w : ℂ => Gamma (ξ - w)) p := by
    have hcomp := (HTGeometry.analyticAt_Gamma_of_re_pos hleft_pos).comp
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => ξ - w) p)
    simpa [Function.comp_def] using hcomp
  have hpow : AnalyticAt ℂ (fun w : ℂ => η ^ (-w)) p :=
    analyticAt_barnesCpow η p hη
  have hval : (fun w : ℂ => Gamma (ξ - w) * η ^ (-w)) p = Gamma (ξ + n) * η ^ n := by
    dsimp [p]
    rw [show ξ - -(n : ℂ) = ξ + n by ring,
      show -(-(n : ℂ)) = (n : ℂ) by ring,
      Complex.cpow_natCast]
  have hreg : Tendsto (fun w : ℂ => Gamma (ξ - w) * η ^ (-w))
      (𝓝[≠] p) (𝓝 (Gamma (ξ + n) * η ^ n)) := by
    rw [← hval]
    exact (hleft.mul hpow).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgamma : Tendsto (fun w : ℂ => (w - p) * Gamma w)
      (𝓝[≠] p) (𝓝 (((-1 : ℂ) ^ n) / (n.factorial : ℂ))) := by
    simpa [p, affineGammaAddPole] using
      (tendsto_affineGammaAdd_residue (0 : ℂ) (b := (1 : ℝ)) (by norm_num) n)
  apply residue_eq_of_tendsto
  convert hreg.mul hgamma using 1
  · funext w
    dsimp [p, barnesJ]
    ring
  · ring

private theorem negNat_mem_barnesRectangle
    (m : ℕ) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) {n : ℕ}
    (hn : n ∈ Finset.range (m + 1)) :
    -(n : ℂ) ∈ Rectangle (barnesLeftCorner m T) (barnesRightCorner c T) := by
  have hRe : (barnesLeftCorner m T).re ≤ (barnesRightCorner c T).re := by
    simp [barnesLeftCorner, barnesRightCorner]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  have hIm : (barnesLeftCorner m T).im ≤ (barnesRightCorner c T).im := by
    simp [barnesLeftCorner, barnesRightCorner]
    linarith
  have hlt : n < m + 1 := Finset.mem_range.mp hn
  have hnm : n ≤ m := by omega
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  rw [mem_Rect hRe hIm]
  constructor
  · have hleft : -((m : ℝ) + 1 / 2) ≤ -(n : ℝ) := by
      linarith
    simpa [barnesLeftCorner] using hleft
  constructor
  · have hright : -(n : ℝ) ≤ c := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith
    simpa [barnesRightCorner] using hright
  constructor
  · have himleft : -T ≤ (0 : ℝ) := by linarith
    simpa [barnesLeftCorner] using himleft
  · have himright : (0 : ℝ) ≤ T := by linarith
    simpa [barnesRightCorner] using himright

/-- Exact finite pole classification for the concrete Barnes integrand in the
half-integral rectangle.  The `Gamma (ξ-w)` factor is regular there because
`Re w ≤ c < Re ξ`; `η^(-w)` is regular and nonzero when `η ≠ 0`. -/
theorem mem_barnesPoleSet_iff
    {ξ η : ℂ} {m : ℕ} {c T : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hT : 0 < T) (hη : η ≠ 0) (q : ℂ) :
    q ∈ Rectangle (barnesLeftCorner m T) (barnesRightCorner c T) ∩
        {z | meromorphicOrderAt (barnesJ ξ η) z < 0} ↔
      q ∈ (barnesPoleFinset m : Set ℂ) := by
  have hRe : (barnesLeftCorner m T).re ≤ (barnesRightCorner c T).re := by
    simp [barnesLeftCorner, barnesRightCorner]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  have hIm : (barnesLeftCorner m T).im ≤ (barnesRightCorner c T).im := by
    simp [barnesLeftCorner, barnesRightCorner]
    linarith
  constructor
  · rintro ⟨hqR, hqPole⟩
    have hqre : q.re ≤ c := by
      simpa [barnesRightCorner] using (mem_Rect hRe hIm q).mp hqR |>.2.1
    change meromorphicOrderAt (barnesJ ξ η) q < 0 at hqPole
    rw [meromorphicOrderAt_barnesJ_eq_Gamma hcξ hη hqre] at hqPole
    have hqGamma : ∃ n : ℕ, q = -(n : ℂ) := by
      by_contra hnot
      push Not at hnot
      rw [Complex.meromorphicOrderAt_Gamma_of_not_neg_nat hnot] at hqPole
      norm_num at hqPole
    rcases hqGamma with ⟨n, hnq⟩
    have hleft : (barnesLeftCorner m T).re ≤ q.re := (mem_Rect hRe hIm q).mp hqR |>.1
    rw [hnq] at hleft
    have hleft' : -((m : ℝ) + 1 / 2) ≤ -(n : ℝ) := by
      simpa [barnesLeftCorner] using hleft
    have hnm : n ≤ m := by
      by_contra hnm
      have hmn : m < n := Nat.lt_of_not_ge hnm
      have hmnR : (m : ℝ) + 1 ≤ n := by
        exact_mod_cast (Nat.succ_le_iff.mpr hmn)
      linarith [hleft']
    have hnrange : n ∈ Finset.range (m + 1) := by
      apply Finset.mem_range.mpr
      omega
    change q ∈ barnesPoleFinset m
    exact Finset.mem_image.mpr ⟨n, hnrange, hnq.symm⟩
  · intro hqP
    change q ∈ barnesPoleFinset m at hqP
    rcases Finset.mem_image.mp hqP with ⟨n, hnrange, hnq⟩
    rw [← hnq]
    constructor
    · exact negNat_mem_barnesRectangle m hc hT hnrange
    · have hqR := negNat_mem_barnesRectangle m hc hT hnrange
      have hqre : (-(n : ℂ)).re ≤ c := by
        simpa [barnesRightCorner] using (mem_Rect hRe hIm _).mp hqR |>.2.1
      change meromorphicOrderAt (barnesJ ξ η) (-(n : ℂ)) < 0
      rw [meromorphicOrderAt_barnesJ_eq_Gamma hcξ hη hqre,
        Complex.meromorphicOrderAt_Gamma_neg_nat]
      exact_mod_cast (show (-1 : ℤ) < 0 by omega)

/-- Set form of `mem_barnesPoleSet_iff`, suitable for subsequent finite
residue summation. -/
theorem barnesPoleSet_eq
    {ξ η : ℂ} {m : ℕ} {c T : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hT : 0 < T) (hη : η ≠ 0) :
    Rectangle (barnesLeftCorner m T) (barnesRightCorner c T) ∩
      {z | meromorphicOrderAt (barnesJ ξ η) z < 0} =
        (barnesPoleFinset m : Set ℂ) := by
  ext q
  exact mem_barnesPoleSet_iff hc hcξ hT hη q

end

end RHTower
