import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheMoebiusGluingOfStars

/-!
# The gcd stratification of the complete Weil family

The Möbius gluing `Q = Q_cop + Σ_{d ≥ 2} (−μ(d)) Q_d` has alternating signs, but they telescope:
`μ ∗ 1 = δ`. Unwound, the gluing is the sign-free **gcd stratification**
(`quadratic_gcd_stratification`):

  `Q(x) = Σ_{g ≤ N} Σ_{gcd(m, n) = g} Q_{mn} x_m x_n`,

and the stratum of `g` is the coprime part of the star of `g`. For the complete Weil family the
star of `g` is the family at the star resolution `(c⌊N/g⌋/N, ⌊N/g⌋)`, entry by entry
(`completeWeilMatrix_star_apply`). So (`completeWeilEnergy_gcd_stratification`)

  `W_{c,N}(x) = Σ_{g ≤ N} Cop(W_{c⌊N/g⌋/N, ⌊N/g⌋})(x(g·))`,

where `Cop` keeps only the coprime pairs.

Every level contributes only its coprime pairs. A coprime pair has no diagonal except at the root
vertex `1` (`coprime_self_iff`), so each stratum is an off-diagonal form, indefinite unless it
vanishes. The successor pairs `(n, n + 1)` are all coprime: the whole successor and archimedean
overlap of consecutive atoms sits in the top stratum `g = 1`. The affine shells `(n, kn + h)` sit
in the stratum `gcd(n, h)`. Local positivity of stars therefore says nothing about the top stratum.
That stratum is the gluing a Kähler-package proof must control.
-/

noncomputable section

open Finset
open scoped RealInnerProductSpace
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticLorentzianGeometry

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- A coprime pair on the diagonal is the root: `gcd(n, n) = 1 ⇔ n = 1`. -/
theorem coprime_self_iff (n : ℕ) : Nat.Coprime n n ↔ n = 1 := Nat.coprime_self n

/-- **The gcd stratification of a quadratic form.** For values `v i ∈ [1, N]`, every form is the
sum over `g ≤ N` of its pairs with `gcd = g`. -/
theorem quadratic_gcd_stratification {ι : Type*} [Fintype ι] {N : ℕ} (v : ι → ℕ)
    (hv : ∀ i, v i ∈ Icc 1 N) (W : ι → ι → ℝ) (x : ι → ℝ) :
    ∑ i, ∑ j, W i j * x i * x j =
      ∑ g ∈ Icc 1 N, ∑ i, ∑ j, if Nat.gcd (v i) (v j) = g then W i j * x i * x j else 0 := by
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  have hg : Nat.gcd (v i) (v j) ∈ Icc 1 N := by
    have h1 := mem_Icc.mp (hv i)
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ (by omega),
      (Nat.gcd_le_left _ (by omega)).trans h1.2⟩
  rw [sum_ite_eq (Icc 1 N) (Nat.gcd (v i) (v j)), if_pos hg]

/-! ### Symmetric matrices are determined by their quadratic forms -/

section Polarization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bil_single_single (A : Matrix ι ι ℝ) (i j : ι) :
    bil A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [bil, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **Polarization.** Two symmetric matrices with the same quadratic form are equal. -/
theorem eq_of_qf_eq {A B : Matrix ι ι ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ v, qf A v = qf B v) : A = B := by
  ext i j
  have hsum := h ((1 : ℝ) • Pi.single i 1 + (1 : ℝ) • Pi.single j 1)
  rw [qf_add_smul hA, qf_add_smul hB, h (Pi.single i 1), h (Pi.single j 1),
    bil_single_single, bil_single_single] at hsum
  linarith

end Polarization

/-! ### The star map at matrix level -/

/-- The star map `a ↦ da` from the horizon `⌊N/d⌋` into the horizon `N`. -/
def starMap {d N : ℕ} (hd : 0 < d) (a : PrimeHorizonIndex (N / d)) : PrimeHorizonIndex N :=
  ⟨d * a, mem_Icc.mpr ⟨Nat.mul_pos hd (mem_Icc.mp a.2).1, by
    have := (Nat.le_div_iff_mul_le hd).mp (mem_Icc.mp a.2).2
    rw [mul_comm]; exact this⟩⟩

theorem starMap_injective {d N : ℕ} (hd : 0 < d) : Function.Injective (starMap (N := N) hd) :=
  fun a b h => Subtype.ext (Nat.eq_of_mul_eq_mul_left hd (congrArg Subtype.val h))

theorem starEmbed_starMap {d N : ℕ} (hd : 0 < d)
    (y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d))) (a : PrimeHorizonIndex (N / d)) :
    starEmbed d N y (starMap hd a) = y a := by
  simp only [starEmbed, starMap, PiLp.toLp_apply, dvd_mul_right, if_true,
    Nat.mul_div_cancel_left _ hd, primeHorizonExtension, dif_pos a.2]

theorem starEmbed_eq_zero {d N : ℕ} (hd : 0 < d)
    (y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d))) (n : PrimeHorizonIndex N)
    (hn : n ∉ Set.range (starMap hd)) : starEmbed d N y n = 0 := by
  simp only [starEmbed, PiLp.toLp_apply]
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    have hn' := (mem_Icc.mp n.2)
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h0
      · simp at ha; omega
      · exact h0
    have haM : a ≤ N / d := (Nat.le_div_iff_mul_le hd).mpr (by rw [mul_comm, ← ha]; exact hn'.2)
    exact absurd ⟨⟨a, mem_Icc.mpr ⟨ha1, haM⟩⟩, Subtype.ext ha.symm⟩ hn
  · rfl

/-- The quadratic form of a star embedding is the form of the restricted matrix. -/
theorem qf_starEmbed {d N : ℕ} (hd : 0 < d) (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
    (y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d))) :
    qf A (fun n => starEmbed d N y n) =
      qf (A.submatrix (starMap hd) (starMap hd)) (fun a => y a) := by
  simp only [qf, bil, dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  symm
  refine Fintype.sum_of_injective (starMap hd) (starMap_injective hd) _ _ (fun n hn => ?_)
    (fun a => ?_)
  · rw [starEmbed_eq_zero hd y n hn, zero_mul]
  · rw [starEmbed_starMap]
    congr 1
    refine Fintype.sum_of_injective (starMap hd) (starMap_injective hd) _ _ (fun n hn => ?_)
      (fun b => by rw [starEmbed_starMap])
    rw [starEmbed_eq_zero hd y n hn, mul_zero]

/-- **The star of the complete Weil matrix is the matrix of the lower resolution**, entry by
entry. -/
theorem completeWeilMatrix_submatrix_starMap {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ)
    {c : ℝ} (hc : 0 < c) {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    (completeWeilMatrix φ c N).submatrix (starMap hd) (starMap hd) =
      completeWeilMatrix φ (starOverlap c N d) (N / d) := by
  refine eq_of_qf_eq ((completeWeilMatrix_isSymm φ c N).submatrix _)
    (completeWeilMatrix_isSymm _ _ _) fun v => ?_
  have h := completeWeilEnergy_starEmbed hφ.contDiff hφ.supp hc hd hdN (WithLp.toLp 2 v)
  rw [completeWeilEnergy_eq_qf, completeWeilEnergy_eq_qf, qf_starEmbed hd] at h
  exact h

/-- **The gcd stratification of the complete Weil family.** `W_{c,N}(x)` is the sum over `g ≤ N`
of the coprime parts of the families at the star resolutions, applied to the pullbacks of `x`. -/
theorem completeWeilEnergy_gcd_stratification {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ)
    {c : ℝ} (hc : 0 < c) (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N x =
      ∑ g ∈ Icc 1 N, ∑ a : PrimeHorizonIndex (N / g), ∑ b : PrimeHorizonIndex (N / g),
        if Nat.Coprime (a : ℕ) b then
          completeWeilMatrix φ (starOverlap c N g) (N / g) a b * starPull g N x a *
            starPull g N x b
        else 0 := by
  have hqf : completeWeilEnergy φ c N x = ∑ i : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
      completeWeilMatrix φ c N i j * x i * x j := by
    rw [completeWeilEnergy_eq_qf, qf, bil, dotProduct]
    refine sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [hqf, quadratic_gcd_stratification (N := N) (fun i : PrimeHorizonIndex N => (i : ℕ))
    (fun i => i.2) (completeWeilMatrix φ c N) (fun i => x i)]
  refine sum_congr rfl fun g hg => ?_
  have hg0 : 0 < g := (mem_Icc.mp hg).1
  have hgN : g ≤ N := (mem_Icc.mp hg).2
  have hpull : ∀ a : PrimeHorizonIndex (N / g), starPull g N x a = x (starMap hg0 a) := by
    intro a
    simp only [starPull, PiLp.toLp_apply, starMap, primeHorizonExtension,
      dif_pos (starMap hg0 a).2]
  have hentry := fun a b => congrFun (congrFun
    (completeWeilMatrix_submatrix_starMap hφ hc hg0 hgN) a) b
  -- Pairs with `gcd = g` are the star images of coprime pairs.
  symm
  refine Fintype.sum_of_injective (starMap hg0) (starMap_injective hg0) _ _ (fun i hi => ?_)
    (fun a => ?_)
  · refine sum_eq_zero fun j _ => if_neg fun hgcd => hi ?_
    have hdvd : g ∣ (i : ℕ) := hgcd ▸ Nat.gcd_dvd_left _ _
    obtain ⟨a, ha⟩ := hdvd
    have hi1 := mem_Icc.mp i.2
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h0
      · simp at ha; omega
      · exact h0
    have haM : a ≤ N / g := (Nat.le_div_iff_mul_le hg0).mpr (by rw [mul_comm, ← ha]; exact hi1.2)
    exact ⟨⟨a, mem_Icc.mpr ⟨ha1, haM⟩⟩, Subtype.ext ha.symm⟩
  · refine Fintype.sum_of_injective (starMap hg0) (starMap_injective hg0) _ _ (fun j hj => ?_)
      (fun b => ?_)
    · refine if_neg fun hgcd => hj ?_
      have hdvd : g ∣ (j : ℕ) := hgcd ▸ Nat.gcd_dvd_right _ _
      obtain ⟨b, hb⟩ := hdvd
      have hj1 := mem_Icc.mp j.2
      have hb1 : 1 ≤ b := by
        rcases Nat.eq_zero_or_pos b with rfl | h0
        · simp at hb; omega
        · exact h0
      have hbM : b ≤ N / g := (Nat.le_div_iff_mul_le hg0).mpr (by rw [mul_comm, ← hb]; exact hj1.2)
      exact ⟨⟨b, mem_Icc.mpr ⟨hb1, hbM⟩⟩, Subtype.ext hb.symm⟩
    · have hgcd : Nat.gcd ((starMap hg0 a : PrimeHorizonIndex N) : ℕ) (starMap hg0 b) = g ↔
          Nat.Coprime (a : ℕ) b := by
        simp only [starMap, Nat.gcd_mul_left, Nat.Coprime]
        constructor
        · intro h; exact Nat.eq_of_mul_eq_mul_left hg0 (h.trans (mul_one g).symm)
        · intro h; rw [h, mul_one]
      by_cases hab : Nat.Coprime (a : ℕ) b
      · rw [if_pos hab, if_pos (hgcd.mpr hab), hpull, hpull, ← hentry]
        rfl
      · rw [if_neg hab, if_neg (fun h => hab (hgcd.mp h))]

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
