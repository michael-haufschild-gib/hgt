import GaloisForLFunctions.RHTower.VisibleCoprimeZetaZeroJet

/-!
# Exact radical of the multiplicity-truncated visible-coprime pairing

The continued kernel annihilates the whole jet rectangle strictly below the two
zeta multiplicities. Adding the next jet in each variable gives precisely one
corner, with the sign already computed by `VisibleCoprimeZetaZeroJet`.

This is a local analytic statement, not a termwise limiting theorem for the
infinite coprime sum or a bound on the actual Mobius integer-prefix energy.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Independent derivative orders in the two-variable product extraction law. -/
theorem complex_mixedAddProductJet_of_separate_vanishing_below
    (i j : ℕ) {f g h : ℂ → ℂ} {a b : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g b)
    (hh : AnalyticAt ℂ h (a + b))
    (hfzero : ∀ k < i, iteratedDeriv k f a = 0)
    (hgzero : ∀ k < j, iteratedDeriv k g b = 0) :
    iteratedDeriv i
        (fun s => iteratedDeriv j (fun t => f s * g t * h (s + t)) b) a =
      iteratedDeriv i f a * iteratedDeriv j g b * h (a + b) := by
  have hnear : ∀ᶠ s in 𝓝 a, ContDiffAt ℂ j h (s + b) := by
    have htend : Tendsto (fun s : ℂ => s + b) (𝓝 a) (𝓝 (a + b)) :=
      continuousAt_id.add continuousAt_const
    exact htend ((hh.contDiffAt (n := j)).eventually (by simp))
  have hinner :
      (fun s => iteratedDeriv j (fun t => f s * g t * h (s + t)) b) =ᶠ[𝓝 a]
        (fun s => iteratedDeriv j g b * (f s * h (s + b))) := by
    filter_upwards [hnear] with s hhs
    have hadd : ContDiffAt ℂ j (fun t : ℂ => s + t) b :=
      contDiffAt_const.add contDiffAt_id
    have hhcomp : ContDiffAt ℂ j (fun t : ℂ => h (s + t)) b := by
      simpa [Function.comp_def] using hhs.comp b hadd
    have hrest : ContDiffAt ℂ j (fun t : ℂ => f s * h (s + t)) b :=
      contDiffAt_const.mul hhcomp
    rw [show (fun t : ℂ => f s * g t * h (s + t)) =
        (fun t : ℂ => g t * (f s * h (s + t))) by funext t; ring]
    exact complex_iteratedDeriv_mul_of_vanishing_below j hg.contDiffAt hrest hgzero
  rw [hinner.iteratedDeriv_eq i]
  have hadd : ContDiffAt ℂ i (fun s : ℂ => s + b) a :=
    contDiffAt_id.add contDiffAt_const
  have hhcomp : ContDiffAt ℂ i (fun s : ℂ => h (s + b)) a := by
    simpa [Function.comp_def] using hh.contDiffAt.comp a hadd
  have hrest : ContDiffAt ℂ i (fun s : ℂ => iteratedDeriv j g b * h (s + b)) a :=
    contDiffAt_const.mul hhcomp
  rw [show (fun s : ℂ => iteratedDeriv j g b * (f s * h (s + b))) =
      (fun s : ℂ => f s * (iteratedDeriv j g b * h (s + b))) by funext s; ring]
  rw [complex_iteratedDeriv_mul_of_vanishing_below i hf.contDiffAt hrest hfzero]
  ring

/-- Entry in the actual Hermitian mixed-jet matrix, with independent orders. -/
def visibleCoprimeZetaJetEntry (rho : XiDivisorSupport) (i j : ℕ) : ℂ :=
  iteratedDeriv i
    (fun s => iteratedDeriv j (fun t => visibleCoprimeZetaKernel s t)
      ((starRingEnd ℂ) (rho : ℂ))) (rho : ℂ)

/-- All entries through the first potentially nonzero jet have a separated formula. -/
theorem visibleCoprimeZetaJetEntry_eq_of_le
    (rho : XiDivisorSupport) {i j : ℕ}
    (hi : i ≤ xiSupportMultiplicity rho) (hj : j ≤ xiSupportMultiplicity rho) :
    visibleCoprimeZetaJetEntry rho i j =
      iteratedDeriv i riemannZeta (rho : ℂ) *
        (starRingEnd ℂ) (iteratedDeriv j riemannZeta (rho : ℂ)) *
        Sieve.invZeta (((2 * (rho : ℂ).re : ℝ) : ℂ)) := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hrho1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hconj1 : (starRingEnd ℂ) (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hh : AnalyticAt ℂ Sieve.invZeta
      ((rho : ℂ) + (starRingEnd ℂ) (rho : ℂ)) := by
    rw [add_conj_eq_ofReal_two_re]
    exact analyticAt_invZeta_of_residueUnit_ne_zero
      (zetaResidueUnit_ne_zero_of_ofReal_pos (by linarith))
  have hraw := complex_mixedAddProductJet_of_separate_vanishing_below i j
    (analyticOn_riemannZeta (rho : ℂ) hrho1)
    (analyticOn_riemannZeta ((starRingEnd ℂ) (rho : ℂ)) hconj1) hh
    (fun k hk => iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity
      rho (lt_of_lt_of_le hk hi))
    (by
      intro k hk
      rw [iteratedDeriv_riemannZeta_conj,
        iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho
          (lt_of_lt_of_le hk hj)]
      simp)
  simpa only [visibleCoprimeZetaJetEntry, visibleCoprimeZetaKernel,
    iteratedDeriv_riemannZeta_conj, add_conj_eq_ofReal_two_re] using hraw

/-- The whole multiplicity-truncated matrix is a single top corner, not a full jet metric. -/
theorem visibleCoprimeZetaJetEntry_eq_corner
    (rho : XiDivisorSupport) {i j : ℕ}
    (hi : i ≤ xiSupportMultiplicity rho) (hj : j ≤ xiSupportMultiplicity rho) :
    visibleCoprimeZetaJetEntry rho i j =
      if i = xiSupportMultiplicity rho ∧ j = xiSupportMultiplicity rho
      then visibleCoprimeZetaMixedJet rho else 0 := by
  by_cases him : i = xiSupportMultiplicity rho
  · subst i
    by_cases hjm : j = xiSupportMultiplicity rho
    · subst j
      simp only [and_self, ↓reduceIte]
      rfl
    · rw [if_neg (by simp [hjm]), visibleCoprimeZetaJetEntry_eq_of_le rho hi hj,
        iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho
          (lt_of_le_of_ne hj hjm)]
      simp
  · rw [if_neg (by simp [him]), visibleCoprimeZetaJetEntry_eq_of_le rho hi hj,
      iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho
        (lt_of_le_of_ne hi him)]
    simp

/-- Pairing of arbitrary coefficient packets through order `m`, inclusive. -/
def visibleCoprimeZetaJetPairing (rho : XiDivisorSupport) (a b : ℕ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range (xiSupportMultiplicity rho + 1),
    ∑ j ∈ Finset.range (xiSupportMultiplicity rho + 1),
      a i * (starRingEnd ℂ) (b j) * visibleCoprimeZetaJetEntry rho i j

/-- Exact one-corner reconstruction for the enlarged jet packet. -/
theorem visibleCoprimeZetaJetPairing_eq_top
    (rho : XiDivisorSupport) (a b : ℕ → ℂ) :
    visibleCoprimeZetaJetPairing rho a b =
      a (xiSupportMultiplicity rho) *
        (starRingEnd ℂ) (b (xiSupportMultiplicity rho)) * visibleCoprimeZetaMixedJet rho := by
  unfold visibleCoprimeZetaJetPairing
  rw [Finset.sum_eq_single (xiSupportMultiplicity rho)]
  · rw [Finset.sum_eq_single (xiSupportMultiplicity rho)]
    · rfl
    · intro j hj hjm
      rw [visibleCoprimeZetaJetEntry_eq_corner rho le_rfl
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), if_neg (by simp [hjm]), mul_zero]
    · simp
  · intro i hi him
    apply Finset.sum_eq_zero
    intro j hj
    rw [visibleCoprimeZetaJetEntry_eq_corner rho
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), if_neg (by simp [him]), mul_zero]
  · simp

/-- Every lower-jet packet is annihilated, at every actual zero, on or off the line. -/
theorem visibleCoprimeZetaPrincipalJetPairing_eq_zero
    (rho : XiDivisorSupport) (a b : ℕ → ℂ) :
    (∑ i ∈ Finset.range (xiSupportMultiplicity rho),
      ∑ j ∈ Finset.range (xiSupportMultiplicity rho),
        a i * (starRingEnd ℂ) (b j) * visibleCoprimeZetaJetEntry rho i j) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  rw [visibleCoprimeZetaJetEntry_eq_corner rho hi'.le hj'.le,
    if_neg (by simp [ne_of_lt hi']), mul_zero]

/-- Exact radical: off the line only the added top coordinate survives;
on the line the whole enlarged packet is radical. -/
theorem visibleCoprimeZetaJetPairing_radical_iff
    (rho : XiDivisorSupport) (a : ℕ → ℂ) :
    (∀ b : ℕ → ℂ, visibleCoprimeZetaJetPairing rho a b = 0) ↔
      a (xiSupportMultiplicity rho) = 0 ∨ (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hone := h (fun _ => 1)
    rw [visibleCoprimeZetaJetPairing_eq_top] at hone
    simp only [map_one, mul_one] at hone
    rcases mul_eq_zero.mp hone with ha | hc
    · exact Or.inl ha
    · exact Or.inr ((visibleCoprimeZetaMixedJet_eq_zero_iff rho).mp hc)
  · rintro (ha | hhalf) b
    · rw [visibleCoprimeZetaJetPairing_eq_top, ha, zero_mul, zero_mul]
    · rw [visibleCoprimeZetaJetPairing_eq_top,
        (visibleCoprimeZetaMixedJet_eq_zero_iff rho).mpr hhalf, mul_zero]

end

end RHTower


