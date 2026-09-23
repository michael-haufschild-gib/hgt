import GaloisForLFunctions.RHTower.ProlateSectorConstrainedGround

/-!
# Every constrained sector eigenvalue is a secular root

The compressed eigenvalue equation on a Fourier sector says that `B g − μ g` annihilates every
vector of the sector with vanishing integral.  Testing it against the two-term combinations
`ℓ_k e_i − ℓ_i e_k`, which are exactly the elementary constrained vectors, forces the coordinate
identity `(d_j − μ) y_j = c ℓ_j`; splitting into real and imaginary parts and pairing with the
constraint then collapses to the secular equation.  With the ground identification this makes the
constrained spectrum of the sector in the first gap exactly the secular root set.
-/

noncomputable section

open Filter Set
open scoped InnerProduct InnerProductSpace

namespace RHTower

theorem inner_even_add_right (u w y : evenSubspace) :
    inner ℂ u (w + y) = inner ℂ u w + inner ℂ u y := inner_add_right u w y

theorem inner_even_sub_right (u w y : evenSubspace) :
    inner ℂ u (w - y) = inner ℂ u w - inner ℂ u y := inner_sub_right u w y

/-- The elementary two-term expansion in a sector. -/
theorem hasSum_sectorPair (a : ℝ) (σ : ℕ → ℕ) {i k : ℕ} (hik : i ≠ k) (b c : ℂ) :
    HasSum (fun j : ℕ => (if j = i then b else if j = k then c else 0) • sectorMode a σ j)
      (b • sectorMode a σ i + c • sectorMode a σ k) := by
  classical
  have h : HasSum (fun j : ℕ => (if j = i then b else if j = k then c else 0) • sectorMode a σ j)
      (∑ j ∈ ({i, k} : Finset ℕ),
        (if j = i then b else if j = k then c else 0) • sectorMode a σ j) :=
    hasSum_sum_of_ne_finset_zero (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp [hj.1, hj.2])
  rw [Finset.sum_pair hik] at h
  simpa [hik, Ne.symm hik] using h

theorem inner_evenCentralIndicator_sectorPair (a : ℝ) (σ : ℕ → ℕ) (i k : ℕ) (b c : ℂ) :
    inner ℂ (evenCentralIndicator a) (b • sectorMode a σ i + c • sectorMode a σ k)
      = b * ((sectorCoord a σ i : ℝ) : ℂ) + c * ((sectorCoord a σ k : ℝ) : ℂ) := by
  rw [inner_even_add_right, inner_even_smul_right, inner_even_smul_right,
    inner_evenCentralIndicator_sectorMode, inner_evenCentralIndicator_sectorMode]

/-- Weak form of the compressed eigenvalue equation on a sector. -/
structure IsSectorConstrainedEigen (a : ℝ) (σ : ℕ → ℕ) (μ : ℝ) (g : evenSubspace) : Prop where
  /-- The vector lies in the sector. -/
  expansion : ∃ x : ℕ → ℂ, HasSum (fun j : ℕ => x j • sectorMode a σ j) g
  /-- It is not the zero vector. -/
  ne_zero : g ≠ 0
  /-- Its integral vanishes. -/
  constraint : inner ℂ (evenCentralIndicator a) g = 0
  /-- The leakage defect is orthogonal to the constrained part of the sector. -/
  weak_eigen : ∀ (z : ℕ → ℂ) (h : evenSubspace),
    HasSum (fun j : ℕ => z j • sectorMode a σ j) h →
    inner ℂ (evenCentralIndicator a) h = 0 →
    inner ℂ (evenProlateLeakage a g - ((μ : ℝ) : ℂ) • g) h = 0

/-- **The converse bridge.**  A constrained sector eigenvalue inside the first spectral gap is a
root of the sector's secular function. -/
theorem infiniteSecular_eq_zero_of_isSectorConstrainedEigen {a : ℝ} (ha : 0 < a)
    {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    (h12 : sectorLeakage a σ 1 < sectorLeakage a σ 2)
    (hd2 : ∀ j, sectorLeakage a σ 2 ≤ sectorLeakage a σ (j + 2))
    (hℓ1 : sectorCoord a σ 1 ≠ 0)
    {μ : ℝ} (hμ : μ ∈ Set.Ioo (sectorLeakage a σ 0) (sectorLeakage a σ 1))
    {g : evenSubspace} (hg : IsSectorConstrainedEigen a σ μ g) :
    infiniteSecular (sectorLeakage a σ) (sectorCoord a σ) μ = 0 := by
  classical
  set D : ℕ → ℝ := sectorLeakage a σ with hDdef
  set L : ℕ → ℝ := sectorCoord a σ with hLdef
  obtain ⟨x, hx⟩ := hg.expansion
  have hvon := orthonormal_sectorMode ha hσ
  have hsumL : Summable fun j : ℕ => L j ^ (2 : ℕ) := summable_sectorCoord_sq a hσ
  -- coordinates of the leakage defect
  have hBg := hasSum_leakage_apply (evenProlateLeakage_apply_sectorMode a σ) hx
  have hcoordB : ∀ j : ℕ,
      inner ℂ (sectorMode a σ j) (evenProlateLeakage a g) = ((D j : ℝ) : ℂ) * x j :=
    fun j => inner_eq_of_hasSum_smul hvon hBg j
  have hcoord : ∀ j : ℕ, inner ℂ (sectorMode a σ j) g = x j :=
    fun j => inner_eq_of_hasSum_smul hvon hx j
  have hdefect : ∀ j : ℕ,
      inner ℂ (evenProlateLeakage a g - ((μ : ℝ) : ℂ) • g) (sectorMode a σ j)
        = (starRingEnd ℂ) ((((D j - μ : ℝ)) : ℂ) * x j) := by
    intro j
    rw [inner_even_conj_symm (evenProlateLeakage a g - ((μ : ℝ) : ℂ) • g) (sectorMode a σ j)]
    congr 1
    rw [inner_even_sub_right, inner_even_smul_right, hcoordB j, hcoord j]
    push_cast
    ring
  -- the two-term test vectors
  have hpair : ∀ i k : ℕ, i ≠ k →
      ((L k : ℝ) : ℂ) * (starRingEnd ℂ) ((((D i - μ : ℝ)) : ℂ) * x i)
        + (-((L i : ℝ) : ℂ)) * (starRingEnd ℂ) ((((D k - μ : ℝ)) : ℂ) * x k) = 0 := by
    intro i k hik
    have hs := hasSum_sectorPair a σ hik ((L k : ℝ) : ℂ) (-((L i : ℝ) : ℂ))
    have hc : inner ℂ (evenCentralIndicator a)
        (((L k : ℝ) : ℂ) • sectorMode a σ i + (-((L i : ℝ) : ℂ)) • sectorMode a σ k) = 0 := by
      rw [inner_evenCentralIndicator_sectorPair]
      ring
    have h0 := hg.weak_eigen _ _ hs hc
    rw [inner_even_add_right, inner_even_smul_right, inner_even_smul_right,
      hdefect i, hdefect k] at h0
    exact h0
  -- the coordinates are proportional to the constraint sequence
  set c : ℝ := (D 1 - μ) * (x 1).re / L 1 with hcdef
  set e : ℝ := (D 1 - μ) * (x 1).im / L 1 with hedef
  have hprop : ∀ j : ℕ, (D j - μ) * (x j).re = c * L j ∧ (D j - μ) * (x j).im = e * L j := by
    intro j
    rcases eq_or_ne j 1 with rfl | hj
    · constructor
      · rw [hcdef]; field_simp
      · rw [hedef]; field_simp
    · have h := hpair j 1 hj
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, Complex.zero_re, Complex.zero_im] at hre him
      constructor
      · rw [hcdef]
        field_simp
        nlinarith [hre, him]
      · rw [hedef]
        field_simp
        nlinarith [hre, him]
  -- the two real coordinate systems
  obtain ⟨hsu, hsw, hsdu, hsdw, hconu, hconw, e1, e2⟩ :=
    sector_real_parts ha hσ hx hg.constraint
  have hne : ∃ j : ℕ, x j ≠ 0 := by
    by_contra hall
    have hz : ∀ j : ℕ, x j = 0 := fun j => not_not.mp fun hj => hall ⟨j, hj⟩
    have hzero : (fun j : ℕ => x j • sectorMode a σ j) = fun _ : ℕ => (0 : evenSubspace) := by
      funext j
      rw [hz j, zero_smul]
    rw [hzero] at hx
    exact hg.ne_zero (hasSum_zero.unique hx).symm
  obtain ⟨j0, hj0⟩ := hne
  by_cases hu : (fun j : ℕ => (x j).re) = 0
  · -- the real part vanishes identically; use the imaginary part
    have hwne : (fun j : ℕ => (x j).im) ≠ 0 := by
      intro hw
      apply hj0
      have h1 : (x j0).re = 0 := congrFun hu j0
      have h2 : (x j0).im = 0 := congrFun hw j0
      exact Complex.ext h1 h2
    exact infiniteSecular_eq_zero_of_constrained_eigen h12 hd2 hsumL hμ
      (c := e) (v := fun j => (x j).im)
      (fun j => by have := (hprop j).2; linarith) hconw hwne
  · exact infiniteSecular_eq_zero_of_constrained_eigen h12 hd2 hsumL hμ
      (c := c) (v := fun j => (x j).re)
      (fun j => by have := (hprop j).1; linarith) hconu hu

end RHTower

end
