import GaloisForLFunctions.HTGeometry.ArchimedeanBracketRatio
import GaloisForLFunctions.HTGeometry.GammaLowestPowerResidue
import GaloisForLFunctions.HTGeometry.GammaShiftShape

/-!
# Dominance among archimedean shapes

The shapes controlling the boundary of `K_G` are `G^k·s^ω·(log s)^b`.  Their comparison is decided
by the same signature triple that governs the Gamma shapes, in the same lexicographic order: the
exponent of the decaying factor first, then the argument exponent, then the logarithm exponent.  So
the combinatorial selection of a dominant member is reused verbatim, and only the analytic decay of
a dominated shape has to be proved.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A power of the archimedean product times an argument power and a logarithm power. -/
def archimedeanShape {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ) (α σ : ℝ)
    (k : ℤ) (ω : ℝ) (b : ℤ) (t : ℝ) : ℂ :=
  (archimedeanProductLine lam μ α σ t) ^ k * gammaShiftShape 0 σ 0 ω b t

theorem archimedeanShape_ne_zero {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hσG : ∀ j, 0 < lam j * σ + (μ j).re) (α : ℝ) (k : ℤ) (ω : ℝ) (b : ℤ) {t : ℝ} (ht : 3 ≤ t) :
    archimedeanShape lam μ α σ k ω b t ≠ 0 := by
  have hσ0 : (0 : ℝ) < σ + 0 := by linarith
  exact mul_ne_zero (zpow_ne_zero _ (archimedeanProductLine_ne_zero lam μ hσG α t))
    (gammaShiftShape_ne_zero hσ0 ht _ _ _)

/-- The ratio of two archimedean shapes splits into the argument-logarithm ratio and a power of the
archimedean product. -/
theorem archimedeanShape_ratio_eq {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ) {σ : ℝ}
    (hσG : ∀ j, 0 < lam j * σ + (μ j).re) (α : ℝ) (k : ℤ) (ω : ℝ) (b : ℤ)
    (k' : ℤ) (ω' : ℝ) (b' : ℤ) (t : ℝ) :
    archimedeanShape lam μ α σ k' ω' b' t / archimedeanShape lam μ α σ k ω b t
      = (gammaShiftShape 0 σ 0 ω' b' t / gammaShiftShape 0 σ 0 ω b t)
        * (archimedeanProductLine lam μ α σ t) ^ (k' - k) := by
  have hP : archimedeanProductLine lam μ α σ t ≠ 0 :=
    archimedeanProductLine_ne_zero lam μ hσG α t
  rw [archimedeanShape, archimedeanShape, mul_div_mul_comm, ← zpow_sub₀ hP, mul_comm]

/-- The argument-logarithm ratio has polynomial growth on the line. -/
theorem hasPolyGrowthLine_gammaShiftShape_ratio {σ : ℝ} (hσ : 0 < σ) (ω : ℝ) (b : ℤ)
    (ω' : ℝ) (b' : ℤ) :
    HasPolyGrowthLine (fun t : ℝ =>
      gammaShiftShape 0 σ 0 ω' b' t / gammaShiftShape 0 σ 0 ω b t) := by
  obtain ⟨m, C, hC, hbound⟩ := hasPolyGrowthLine_cpow_mul_vertLog σ (ω' - ω) (b' - b)
  refine ⟨m, C, hC, ?_⟩
  have hσ0 : (0 : ℝ) < σ + 0 := by linarith
  filter_upwards [hbound, eventually_ge_atTop (3 : ℝ)] with t hbt ht
  have hval : gammaShiftShape 0 σ 0 ω' b' t / gammaShiftShape 0 σ 0 ω b t
      = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ ((ω' - ω : ℝ) : ℂ) * vertLog t ^ (b' - b) := by
    rw [gammaShiftShape_div hσ0 ht, gammaShiftShape]
    simp
  rw [hval]
  exact hbt

/-- **A dominated archimedean shape is negligible against the dominating one.** -/
theorem tendsto_archimedeanShape_ratio_zero {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ)
    (hlam : ∀ j, 0 < lam j) (hd : 0 < d) {σ : ℝ} (hσ : 0 < σ)
    (hσG : ∀ j, 0 < lam j * σ + (μ j).re) (α : ℝ)
    {k : ℤ} {ω : ℝ} {b : ℤ} {k' : ℤ} {ω' : ℝ} {b' : ℤ}
    (h : ShiftShapeDominates k ω b k' ω' b') :
    Tendsto (fun t : ℝ => archimedeanShape lam μ α σ k' ω' b' t
        / archimedeanShape lam μ α σ k ω b t) atTop (nhds 0) := by
  have hσ0 : (0 : ℝ) < σ + 0 := by linarith
  have hsplit : ∀ᶠ t : ℝ in atTop,
      archimedeanShape lam μ α σ k' ω' b' t / archimedeanShape lam μ α σ k ω b t
        = (gammaShiftShape 0 σ 0 ω' b' t / gammaShiftShape 0 σ 0 ω b t)
          * (archimedeanProductLine lam μ α σ t) ^ (k' - k) := by
    filter_upwards with t
    exact archimedeanShape_ratio_eq lam μ hσG α k ω b k' ω' b' t
  rcases h with hk | hrest
  · -- a strictly higher power of the archimedean product wins outright
    obtain ⟨m, C, hC, hbound⟩ := hasPolyGrowthLine_gammaShiftShape_ratio hσ ω b ω' b'
    have hn : (((k' - k).toNat : ℕ) : ℤ) = k' - k := Int.toNat_of_nonneg (by omega)
    have hpos : 0 < (k' - k).toNat := by omega
    have hzero := tendsto_polyGrowth_mul_archimedeanProduct_pow_zero lam μ hlam hσG α hd
      hC hbound hpos
    refine Filter.Tendsto.congr' ?_ hzero
    filter_upwards [hsplit] with t hst
    rw [hst, ← zpow_natCast (archimedeanProductLine lam μ α σ t) ((k' - k).toNat), hn]
  · have hkk : k' = k := by rcases hrest with ⟨h1, -⟩ | ⟨h1, -, -⟩ <;> exact h1
    have hgamma : Tendsto (fun t : ℝ =>
        gammaShiftShape 0 σ 0 ω' b' t / gammaShiftShape 0 σ 0 ω b t) atTop (nhds 0) := by
      refine tendsto_gammaShiftShape_ratio_zero (lam := 0) hσ0 ?_
      rcases hrest with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr ⟨rfl, h2, h3⟩)
    refine Filter.Tendsto.congr' ?_ hgamma
    filter_upwards [hsplit] with t hst
    rw [hst, hkk]
    simp

/-- The dominant ratio at a **named** dominant index, with the limit given by an explicit formula:
the residue quotient at a tie and zero at a strictly dominated member.  Naming the index is what
lets one dominant member serve every abscissa of a tube at once. -/
theorem tendsto_archimedeanShape_dominantRatio {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ)
    (hlam : ∀ j, 0 < lam j) (hd : 0 < d) {σ : ℝ} (hσ : 0 < σ)
    (hσG : ∀ j, 0 < lam j * σ + (μ j).re) (α : ℝ)
    {N : ℕ} (F : Fin N → ℝ → ℂ) (k : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ)
    (c : Fin N → ℂ) (hc : ∀ a, c a ≠ 0)
    (hdat : ∀ a, Tendsto (fun t => F a t / archimedeanShape lam μ α σ (k a) (ω a) (b a) t)
      atTop (nhds (c a)))
    (β : Fin N)
    (hβ : ∀ a : Fin N, (k a = k β ∧ ω a = ω β ∧ b a = b β)
      ∨ ShiftShapeDominates (k β) (ω β) (b β) (k a) (ω a) (b a)) :
    ∀ a : Fin N, Tendsto (fun t => F a t / F β t) atTop
      (nhds (if (k a = k β ∧ ω a = ω β ∧ b a = b β) then c a * (c β)⁻¹ else 0)) := by
  classical
  have hinv : Tendsto (fun t => (F β t / archimedeanShape lam μ α σ (k β) (ω β) (b β) t)⁻¹)
      atTop (nhds (c β)⁻¹) := (hdat β).inv₀ (hc β)
  have hFβ : ∀ᶠ t : ℝ in atTop, F β t ≠ 0 := by
    filter_upwards [(hdat β).eventually_ne (hc β)] with t hne
    exact (div_ne_zero_iff.mp hne).1
  intro a
  by_cases htie : k a = k β ∧ ω a = ω β ∧ b a = b β
  · rw [if_pos htie]
    obtain ⟨h1, h2, h3⟩ := htie
    refine Filter.Tendsto.congr' ?_ ((hdat a).mul hinv)
    filter_upwards [eventually_ge_atTop (3 : ℝ), hFβ] with t ht hFβt
    have hSβ : archimedeanShape lam μ α σ (k β) (ω β) (b β) t ≠ 0 :=
      archimedeanShape_ne_zero lam μ hσ hσG α _ _ _ ht
    have hshape : archimedeanShape lam μ α σ (k a) (ω a) (b a) t
        = archimedeanShape lam μ α σ (k β) (ω β) (b β) t := by rw [h1, h2, h3]
    rw [hshape]
    field_simp
  · rw [if_neg htie]
    have hdom : ShiftShapeDominates (k β) (ω β) (b β) (k a) (ω a) (b a) := by
      rcases hβ a with heq | hdom
      · exact absurd heq htie
      · exact hdom
    have hratio := tendsto_archimedeanShape_ratio_zero lam μ hlam hd hσ hσG α hdom
    have hmul := ((hdat a).mul hratio).mul hinv
    rw [mul_zero, zero_mul] at hmul
    refine Filter.Tendsto.congr' ?_ hmul
    filter_upwards [eventually_ge_atTop (3 : ℝ), hFβ] with t ht hFβt
    have hSa : archimedeanShape lam μ α σ (k a) (ω a) (b a) t ≠ 0 :=
      archimedeanShape_ne_zero lam μ hσ hσG α _ _ _ ht
    have hSβ : archimedeanShape lam μ α σ (k β) (ω β) (b β) t ≠ 0 :=
      archimedeanShape_ne_zero lam μ hσ hσG α _ _ _ ht
    field_simp

/-- **The projective boundary of a finite family in the archimedean field.**  Every nonzero finite
tuple has a member against which all the ratios converge, and the ratio at that member is one.  This
is equation `(8)`. -/
theorem exists_dominant_archimedeanShape_ratio {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ)
    (hlam : ∀ j, 0 < lam j) (hd : 0 < d) {σ : ℝ} (hσ : 0 < σ)
    (hσG : ∀ j, 0 < lam j * σ + (μ j).re) (α : ℝ)
    {N : ℕ} (hN : 0 < N) (F : Fin N → ℝ → ℂ) (k : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ)
    (c : Fin N → ℂ) (hc : ∀ a, c a ≠ 0)
    (hdat : ∀ a, Tendsto (fun t => F a t / archimedeanShape lam μ α σ (k a) (ω a) (b a) t)
      atTop (nhds (c a))) :
    ∃ (β : Fin N) (rr : Fin N → ℂ), rr β = 1 ∧
      ∀ a : Fin N, Tendsto (fun t => F a t / F β t) atTop (nhds (rr a)) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shiftShape_index hN k ω b
  refine ⟨β, fun a => if (k a = k β ∧ ω a = ω β ∧ b a = b β) then c a * (c β)⁻¹ else 0, ?_,
    tendsto_archimedeanShape_dominantRatio lam μ hlam hd hσ hσG α F k ω b c hc hdat β hβ⟩
  dsimp only
  rw [if_pos ⟨rfl, rfl, rfl⟩, mul_inv_cancel₀ (hc β)]

end

end GaloisForLFunctions.HTGeometry
