import GaloisForLFunctions.RHTower.Sieve.GuthMaynardAffineEquidistribution
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropEightOneHolder

set_option autoImplicit false

/-!
# The frequency box of Proposition 7.2 as affine sums (towards Proposition 10.1)

Proposition 7.2 of Guth–Maynard sums over frequency triples in the box
`M₁ ≤ |m₁| < 2M₁`, `M ≤ |m₂| < 2M`, `M ≤ |m₃| < 9M` (`InPropSevenTwoBox`). In the proof of
Proposition 10.1 the two square functions

`Q(v) = Σ_m f((m₁v + m₃)/m₂)`,   `P(v) = Σ_m f((m₁v + m₃)/(m₂v))`   (`v ∈ [1/2, 2]`)

are compared with the affine sums `A(u) = Σ_{|m₁| ∼ M₁', m₂ ∼ M₂', |m₃| ≤ M₃'} f((m₁u + m₃)/m₂)`
of `GuthMaynardAffineSum`, for `f ≥ 0`:

* `Q(v) ≤ 2 A(v)` at scales `(M₁ − ½, M − ½, 9M)` (`sum_box_le_affineSum`): the triples with
  `m₂ > 0` embed into the affine index set, those with `m₂ < 0` embed after `m ↦ −m`;
* `P(v) = h(1/v)` with `h(u) = Σ_m f((m₃u + m₁)/m₂)`, and splitting `M ≤ |m₃| < 9M` into four
  dyadic shells `2^k M ≤ |m₃| < 2^{k+1} M` gives `h ≤ 2 Σ_{k<4} A_k` at scales
  `(2^k M − ½, M − ½, 2M₁)` (`sum_box_swap_le_affineSum`).

Consequently (`setIntegral_sq_sum_box_le`, `setIntegral_sq_sum_box_mobius_le`, with the inversion
`v ↦ 1/v` of Jacobian `≥ 1/4` on `[1/2, 2]`):

`∫_{1/2}^{2} Q² ≤ 4 J_{16M}(f)`,   `∫_{1/2}^{2} P² ≤ 256 J_{16M}(f)`.
-/

open MeasureTheory Finset Set

namespace RHTower.GuthMaynard

noncomputable section

/-- The frequency box of Proposition 7.2: `M₁ ≤ |m₁| < 2M₁`, `M ≤ |m₂| < 2M`, `M ≤ |m₃| < 9M`. -/
def InPropSevenTwoBox (M₁ M : ℕ) (m : ℤ × ℤ × ℤ) : Prop :=
  (M₁ : ℤ) ≤ |m.1| ∧ |m.1| < 2 * M₁ ∧ (M : ℤ) ≤ |m.2.1| ∧ |m.2.1| < 2 * M ∧ (M : ℤ) ≤ |m.2.2| ∧
    |m.2.2| < 9 * M

/-- Comparison of finite sums along an injection into a larger index set with nonnegative
summands. -/
theorem sum_le_sum_of_injOn {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    {φ : α → β} (hφ : Set.InjOn φ s) (hst : ∀ a ∈ s, φ a ∈ t) {F : α → ℝ} {G : β → ℝ}
    (hG : ∀ b ∈ t, 0 ≤ G b) (hFG : ∀ a ∈ s, F a ≤ G (φ a)) : ∑ a ∈ s, F a ≤ ∑ b ∈ t, G b :=
  calc ∑ a ∈ s, F a ≤ ∑ a ∈ s, G (φ a) := Finset.sum_le_sum hFG
    _ = ∑ b ∈ s.image φ, G b := (Finset.sum_image hφ).symm
    _ ≤ ∑ b ∈ t, G b := Finset.sum_le_sum_of_subset_of_nonneg
        (fun b hb => by obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb; exact hst a ha)
        fun b hb _ => hG b hb

/-! ### Memberships -/

theorem mem_dyadicInt_of {a : ℕ} {m : ℤ} (h1 : (a : ℤ) ≤ |m|) (h2 : |m| < 2 * a) :
    m ∈ dyadicInt ((a : ℝ) - 1 / 2) := by
  rw [mem_dyadicInt]
  have h1' : (a : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast h1
  have h2' : |(m : ℝ)| + 1 ≤ 2 * a := by
    have : |m| + 1 ≤ 2 * a := by omega
    exact_mod_cast this
  constructor <;> linarith

theorem mem_dyadicNat_toNat {a : ℕ} {m : ℤ} (h1 : (a : ℤ) ≤ m) (h2 : m < 2 * a) :
    m.toNat ∈ dyadicNat ((a : ℝ) - 1 / 2) := by
  rw [mem_dyadicNat]
  have hm : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    rw [show ((m.toNat : ℕ) : ℝ) = (((m.toNat : ℕ) : ℤ) : ℝ) from rfl,
      Int.toNat_of_nonneg (by omega)]
  rw [hm]
  have h1' : (a : ℝ) ≤ m := by exact_mod_cast h1
  have h2' : (m : ℝ) + 1 ≤ 2 * a := by
    have : m + 1 ≤ 2 * a := by omega
    exact_mod_cast this
  constructor <;> linarith

theorem mem_centredInt_of {b : ℕ} {m : ℤ} (h : |m| < b) : m ∈ centredInt (b : ℝ) := by
  rw [mem_centredInt]
  have : |m| ≤ b := h.le
  exact_mod_cast this

/-- The affine sum as a sum over the product index set. -/
theorem affineSum_eq_sum_product (f : ℝ → ℝ) (M₁ M₂ M₃ u : ℝ) :
    affineSum f M₁ M₂ M₃ u = ∑ p ∈ dyadicInt M₁ ×ˢ (dyadicNat M₂ ×ˢ centredInt M₃),
      f ((p.1 * u + p.2.2) / p.2.1) := by
  rw [affineSum, Finset.sum_product]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.sum_product]

/-- `((m.toNat : ℕ) : ℝ) = m` for `m ≥ 0`. -/
theorem natCast_toNat_of_nonneg {m : ℤ} (hm : 0 ≤ m) : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
  rw [show ((m.toNat : ℕ) : ℝ) = (((m.toNat : ℕ) : ℤ) : ℝ) from rfl, Int.toNat_of_nonneg hm]

/-! ### The two sign classes of `m₂` -/

/-- A sum over a set of triples with `a ≤ |m₂| < 2a` splits by the sign of `m₂`, each class
embedding into a product index set `I × dyadicNat (a − ½) × J` by `m ↦ (±π₁ m, |m₂|, ±π₃ m)`. -/
theorem sum_le_two_mul_sum_product {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) {a : ℕ}
    (𝓜 : Finset (ℤ × ℤ × ℤ)) (I J : Finset ℤ) (π₁ π₃ : ℤ × ℤ × ℤ → ℤ)
    (hπ : ∀ m ∈ 𝓜, ∀ m' ∈ 𝓜, π₁ m = π₁ m' → π₃ m = π₃ m' → m.2.1 = m'.2.1 → m = m')
    (hπneg : ∀ m ∈ 𝓜, ∀ m' ∈ 𝓜, -π₁ m = -π₁ m' → -π₃ m = -π₃ m' → -m.2.1 = -m'.2.1 → m = m')
    (h₂ : ∀ m ∈ 𝓜, (a : ℤ) ≤ |m.2.1| ∧ |m.2.1| < 2 * a)
    (hI : ∀ m ∈ 𝓜, π₁ m ∈ I ∧ -π₁ m ∈ I) (hJ : ∀ m ∈ 𝓜, π₃ m ∈ J ∧ -π₃ m ∈ J) (u : ℝ) :
    ∑ m ∈ 𝓜, f ((π₁ m * u + π₃ m) / m.2.1) ≤
      2 * ∑ p ∈ I ×ˢ (dyadicNat ((a : ℝ) - 1 / 2) ×ˢ J), f ((p.1 * u + p.2.2) / p.2.1) := by
  classical
  set G : ℤ × ℕ × ℤ → ℝ := fun p => f ((p.1 * u + p.2.2) / p.2.1) with hG
  have hG0 : ∀ p ∈ I ×ˢ (dyadicNat ((a : ℝ) - 1 / 2) ×ˢ J), 0 ≤ G p := fun p _ => hf0 _
  rw [← Finset.sum_filter_add_sum_filter_not 𝓜 (fun m => 0 < m.2.1), two_mul]
  refine add_le_add ?_ ?_
  · -- `m₂ > 0`
    refine sum_le_sum_of_injOn (φ := fun m => (π₁ m, m.2.1.toNat, π₃ m)) ?_ ?_ hG0 ?_
    · intro m hm m' hm' h
      obtain ⟨hm, hpos⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm', hpos'⟩ := Finset.mem_filter.mp hm'
      simp only [Prod.mk.injEq] at h
      exact hπ m hm m' hm' h.1 h.2.2 (by omega)
    · intro m hm
      obtain ⟨hm, hpos⟩ := Finset.mem_filter.mp hm
      obtain ⟨h1, h2⟩ := h₂ m hm
      rw [abs_of_pos hpos] at h1 h2
      exact Finset.mem_product.mpr ⟨(hI m hm).1, Finset.mem_product.mpr
        ⟨mem_dyadicNat_toNat h1 h2, (hJ m hm).1⟩⟩
    · intro m hm
      obtain ⟨-, hpos⟩ := Finset.mem_filter.mp hm
      rw [natCast_toNat_of_nonneg hpos.le]
  · -- `m₂ < 0`
    refine sum_le_sum_of_injOn (φ := fun m => (-π₁ m, (-m.2.1).toNat, -π₃ m)) ?_ ?_ hG0 ?_
    · intro m hm m' hm' h
      obtain ⟨hm, hneg⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm', hneg'⟩ := Finset.mem_filter.mp hm'
      simp only [Prod.mk.injEq] at h
      exact hπneg m hm m' hm' h.1 h.2.2 (by omega)
    · intro m hm
      obtain ⟨hm, hneg⟩ := Finset.mem_filter.mp hm
      obtain ⟨h1, h2⟩ := h₂ m hm
      rw [abs_of_nonpos (not_lt.mp hneg)] at h1 h2
      exact Finset.mem_product.mpr ⟨(hI m hm).2, Finset.mem_product.mpr
        ⟨mem_dyadicNat_toNat h1 h2, (hJ m hm).2⟩⟩
    · intro m hm
      obtain ⟨hm, hneg⟩ := Finset.mem_filter.mp hm
      have hneg' : m.2.1 ≤ 0 := not_lt.mp hneg
      rw [natCast_toNat_of_nonneg (by omega)]
      apply le_of_eq
      congr 1
      push_cast
      rw [show -(π₁ m : ℝ) * u + -(π₃ m : ℝ) = -((π₁ m : ℝ) * u + π₃ m) by ring, neg_div_neg_eq]

/-! ### The square functions as affine sums -/

/-- `Q(v) = Σ_m f((m₁v + m₃)/m₂) ≤ 2 A(v)` at scales `(M₁ − ½, M − ½, 9M)`. -/
theorem sum_box_le_affineSum {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) {M₁ M : ℕ}
    (𝓜 : Finset (ℤ × ℤ × ℤ)) (h𝓜 : ∀ m ∈ 𝓜, InPropSevenTwoBox M₁ M m) (v : ℝ) :
    ∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / m.2.1) ≤
      2 * affineSum f ((M₁ : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2) ((9 * M : ℕ) : ℝ) v := by
  rw [affineSum_eq_sum_product]
  refine sum_le_two_mul_sum_product hf0 𝓜 _ _ (fun m => m.1) (fun m => m.2.2) ?_ ?_
    (fun m hm => ⟨(h𝓜 m hm).2.2.1, (h𝓜 m hm).2.2.2.1⟩) ?_ ?_ v
  · intro m _ m' _ h1 h3 h2
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro m _ m' _ h1 h3 h2
    exact Prod.ext (neg_inj.mp h1) (Prod.ext (neg_inj.mp h2) (neg_inj.mp h3))
  · intro m hm
    obtain ⟨h1, h2, -⟩ := h𝓜 m hm
    exact ⟨mem_dyadicInt_of h1 h2, mem_dyadicInt_of (by rwa [abs_neg]) (by rwa [abs_neg])⟩
  · intro m hm
    obtain ⟨-, -, -, -, -, h6⟩ := h𝓜 m hm
    have h6' : |m.2.2| < ((9 * M : ℕ) : ℤ) := by push_cast; exact h6
    exact ⟨mem_centredInt_of h6', mem_centredInt_of (by rwa [abs_neg])⟩

/-- `h(u) = Σ_m f((m₃u + m₁)/m₂) ≤ 2 Σ_{k<4} A_k(u)`, `A_k` at scales `(2^k M − ½, M − ½, 2M₁)`:
the four dyadic shells `2^k M ≤ |m₃| < 2^{k+1} M` cover `M ≤ |m₃| < 9M`. -/
theorem sum_box_swap_le_affineSum {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) {M₁ M : ℕ}
    (𝓜 : Finset (ℤ × ℤ × ℤ)) (h𝓜 : ∀ m ∈ 𝓜, InPropSevenTwoBox M₁ M m) (u : ℝ) :
    ∑ m ∈ 𝓜, f ((m.2.2 * u + m.1) / m.2.1) ≤
      2 * ∑ k ∈ range 4, affineSum f (((2 ^ k * M : ℕ) : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2)
        ((2 * M₁ : ℕ) : ℝ) u := by
  classical
  set shell : ℕ → ℤ × ℤ × ℤ → Prop := fun k m => ((2 ^ k * M : ℕ) : ℤ) ≤ |m.2.2| ∧
    |m.2.2| < 2 * ((2 ^ k * M : ℕ) : ℤ) with hshell
  -- every triple of the box lies in one of the four shells
  have hcover : ∀ m ∈ 𝓜, f ((m.2.2 * u + m.1) / m.2.1) ≤
      ∑ k ∈ range 4, if shell k m then f ((m.2.2 * u + m.1) / m.2.1) else 0 := by
    intro m hm
    obtain ⟨-, -, -, -, h5, h6⟩ := h𝓜 m hm
    have hex : ∃ k ∈ range 4, shell k m := by
      simp only [hshell]
      push_cast
      by_cases a1 : |m.2.2| < 2 * M
      · exact ⟨0, by simp, by simpa using h5, by simpa using a1⟩
      by_cases a2 : |m.2.2| < 4 * M
      · exact ⟨1, by simp, by push_cast; linarith, by push_cast; linarith⟩
      by_cases a3 : |m.2.2| < 8 * M
      · exact ⟨2, by simp, by push_cast; linarith, by push_cast; linarith⟩
      exact ⟨3, by simp, by push_cast; linarith, by push_cast; linarith⟩
    obtain ⟨k, hk, hks⟩ := hex
    calc f ((m.2.2 * u + m.1) / m.2.1)
        = if shell k m then f ((m.2.2 * u + m.1) / m.2.1) else 0 := by rw [if_pos hks]
      _ ≤ ∑ k ∈ range 4, if shell k m then f ((m.2.2 * u + m.1) / m.2.1) else 0 :=
          Finset.single_le_sum (f := fun k => if shell k m then f ((m.2.2 * u + m.1) / m.2.1)
            else 0) (fun k _ => by split_ifs <;> simp [hf0]) hk
  refine (Finset.sum_le_sum hcover).trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← Finset.sum_filter, affineSum_eq_sum_product]
  refine sum_le_two_mul_sum_product hf0 (𝓜.filter (shell k)) _ _ (fun m => m.2.2) (fun m => m.1)
    ?_ ?_ (fun m hm => ⟨(h𝓜 m (Finset.mem_filter.mp hm).1).2.2.1,
      (h𝓜 m (Finset.mem_filter.mp hm).1).2.2.2.1⟩) ?_ ?_ u
  · intro m _ m' _ h3 h1 h2
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro m _ m' _ h3 h1 h2
    exact Prod.ext (neg_inj.mp h1) (Prod.ext (neg_inj.mp h2) (neg_inj.mp h3))
  · intro m hm
    obtain ⟨-, hs1, hs2⟩ := Finset.mem_filter.mp hm
    exact ⟨mem_dyadicInt_of hs1 hs2, mem_dyadicInt_of (by rwa [abs_neg]) (by rwa [abs_neg])⟩
  · intro m hm
    obtain ⟨-, h2, -⟩ := h𝓜 m (Finset.mem_filter.mp hm).1
    have h2' : |m.1| < ((2 * M₁ : ℕ) : ℤ) := by push_cast; exact h2
    exact ⟨mem_centredInt_of h2', mem_centredInt_of (by rwa [abs_neg])⟩

/-! ### The square integrals -/

theorem cast_ne_zero_of_box {M : ℕ} (hM : 1 ≤ M) {x : ℤ} (h : (M : ℤ) ≤ |x|) : (x : ℝ) ≠ 0 := by
  have : x ≠ 0 := fun h0 => by rw [h0, abs_zero] at h; omega
  exact_mod_cast this

/-- `h(u) = Σ_m f((m₃u + m₁)/m₂)` lies in every `Lᵖ`. -/
theorem memLp_sum_box_swap {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {M₁ M : ℕ} (hM : 1 ≤ M) (𝓜 : Finset (ℤ × ℤ × ℤ))
    (h𝓜 : ∀ m ∈ 𝓜, InPropSevenTwoBox M₁ M m) (p : ENNReal) :
    MemLp (fun u => ∑ m ∈ 𝓜, f ((m.2.2 * u + m.1) / m.2.1)) p :=
  memLp_finsetSum _ fun m hm => memLp_affine_term hf hfc
    (cast_ne_zero_of_box hM (h𝓜 m hm).2.2.2.2.1) (cast_ne_zero_of_box hM (h𝓜 m hm).2.2.1) _ p

/-- **The affine square function.** `∫_{1/2}^{2} Q² ≤ 4 ∫ A²` at scales `(M₁ − ½, M − ½, 9M)`. -/
theorem setIntegral_sq_sum_box_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {M₁ M : ℕ} (𝓜 : Finset (ℤ × ℤ × ℤ))
    (h𝓜 : ∀ m ∈ 𝓜, InPropSevenTwoBox M₁ M m) :
    ∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / m.2.1)) ^ 2 ≤
      4 * affineEnergy f ((M₁ : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2) ((9 * M : ℕ) : ℝ) := by
  set A := affineSum f ((M₁ : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2) ((9 * M : ℕ) : ℝ) with hA
  have hAi : Integrable fun v => 4 * A v ^ 2 :=
    ((memLp_affineSum hf hfc _ _ _ 2).integrable_sq).const_mul 4
  calc ∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / m.2.1)) ^ 2
      ≤ ∫ v in Icc (1 / 2 : ℝ) 2, 4 * A v ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => sq_nonneg _)
          hAi.integrableOn (Filter.Eventually.of_forall fun v => ?_)
        have h1 := sum_box_le_affineSum hf0 𝓜 h𝓜 v
        have h0 : 0 ≤ ∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / m.2.1) := Finset.sum_nonneg fun _ _ => hf0 _
        calc (∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / m.2.1)) ^ 2 ≤ (2 * A v) ^ 2 :=
              pow_le_pow_left₀ h0 h1 2
          _ = 4 * A v ^ 2 := by ring
    _ ≤ ∫ v, 4 * A v ^ 2 :=
        setIntegral_le_integral hAi (Filter.Eventually.of_forall fun v => by positivity)
    _ = 4 * affineEnergy f ((M₁ : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2) ((9 * M : ℕ) : ℝ) := by
        rw [integral_const_mul]
        rfl

/-- **The Möbius square function.** `∫_{1/2}^{2} P² ≤ 64 Σ_{k<4} ∫ A_k²`, with
`P(v) = Σ_m f((m₁v + m₃)/(m₂v))` and `A_k` at scales `(2^k M − ½, M − ½, 2M₁)`. -/
theorem setIntegral_sq_sum_box_mobius_le {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) {M₁ M : ℕ} (hM : 1 ≤ M)
    (𝓜 : Finset (ℤ × ℤ × ℤ)) (h𝓜 : ∀ m ∈ 𝓜, InPropSevenTwoBox M₁ M m) :
    ∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / (m.2.1 * v))) ^ 2 ≤
      64 * ∑ k ∈ range 4, affineEnergy f (((2 ^ k * M : ℕ) : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2)
        ((2 * M₁ : ℕ) : ℝ) := by
  set h : ℝ → ℝ := fun u => ∑ m ∈ 𝓜, f ((m.2.2 * u + m.1) / m.2.1) with hh
  set A : ℕ → ℝ → ℝ := fun k => affineSum f (((2 ^ k * M : ℕ) : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2)
    ((2 * M₁ : ℕ) : ℝ) with hA
  have hpos : ∀ v ∈ Icc (1 / 2 : ℝ) 2, 0 < v := fun v hv => by linarith [hv.1]
  -- `P(v) = h(1/v)`
  have hPh : ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      (∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / (m.2.1 * v))) ^ 2 = h v⁻¹ ^ 2 := fun v hv => by
    have hv0 := (hpos v hv).ne'
    simp only [hh]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have h₂ := cast_ne_zero_of_box hM (h𝓜 m hm).2.2.1
    congr 1
    field_simp
    ring
  have hcont : Continuous h := continuous_finsetSum _ fun m _ => continuous_affine_term hf _ _ _
  have hhL := memLp_sum_box_swap hf hfc hM 𝓜 h𝓜 2
  -- the inversion `v ↦ 1/v` on `[1/2, 2]`
  have hinv : ∫ v in Icc (1 / 2 : ℝ) 2, h v⁻¹ ^ 2 ≤ (1 / 4 : ℝ)⁻¹ * ∫ u, h u ^ 2 := by
    refine setIntegral_comp_le_inv_mul_integral (S := Icc (1 / 2 : ℝ) 2) measurableSet_Icc
      (φ := fun v => v⁻¹) (φ' := fun v => -(v ^ 2)⁻¹)
      (fun v hv => (hasDerivAt_inv (hpos v hv).ne').hasDerivWithinAt) inv_injective.injOn
      (by norm_num) (fun v hv => ?_) hhL.integrable_sq (fun u => sq_nonneg _) ?_
    · have hv0 := hpos v hv
      rw [abs_neg, abs_of_pos (by positivity), le_inv_comm₀ (by norm_num) (by positivity)]
      nlinarith [hv.2]
    · refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
      exact ((hcont.comp_continuousOn (continuousOn_inv₀.mono fun v hv =>
        (hpos v hv).ne')).pow 2)
  -- `h ≤ 2 Σ_k A_k`
  have hAi : ∀ k ∈ range 4, Integrable fun u => A k u ^ 2 := fun k _ =>
    (memLp_affineSum hf hfc _ _ _ 2).integrable_sq
  have hsq : ∫ u, h u ^ 2 ≤ 16 * ∑ k ∈ range 4, ∫ u, A k u ^ 2 := by
    rw [← integral_finsetSum _ hAi, ← integral_const_mul]
    refine integral_mono hhL.integrable_sq ((integrable_finsetSum _ hAi).const_mul _)
      fun u => ?_
    have h1 := sum_box_swap_le_affineSum hf0 𝓜 h𝓜 u
    have h0 : 0 ≤ h u := Finset.sum_nonneg fun _ _ => hf0 _
    have hcs := sq_sum_le_card_mul_sum_sq (s := range 4) (f := fun k => A k u)
    rw [Finset.card_range] at hcs
    calc h u ^ 2 ≤ (2 * ∑ k ∈ range 4, A k u) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * (∑ k ∈ range 4, A k u) ^ 2 := by ring
      _ ≤ 4 * ((4 : ℕ) * ∑ k ∈ range 4, A k u ^ 2) := by gcongr
      _ = 16 * ∑ k ∈ range 4, A k u ^ 2 := by push_cast; ring
  calc ∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / (m.2.1 * v))) ^ 2
      = ∫ v in Icc (1 / 2 : ℝ) 2, h v⁻¹ ^ 2 := setIntegral_congr_fun measurableSet_Icc hPh
    _ ≤ (1 / 4 : ℝ)⁻¹ * ∫ u, h u ^ 2 := hinv
    _ ≤ 4 * (16 * ∑ k ∈ range 4, ∫ u, A k u ^ 2) := by
        rw [show (1 / 4 : ℝ)⁻¹ = 4 by norm_num]
        exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 64 * ∑ k ∈ range 4, affineEnergy f (((2 ^ k * M : ℕ) : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2)
          ((2 * M₁ : ℕ) : ℝ) := by
        rw [← mul_assoc, show (4 : ℝ) * 16 = 64 by norm_num]
        rfl

/-- The scales of both square functions lie in the window of `J_{16M}`. -/
theorem affineEnergy_box_le_affineSup {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {M₁ M : ℕ} (hM₁ : 1 ≤ M₁) (hM₁M : M₁ ≤ M) :
    affineEnergy f ((M₁ : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2) ((9 * M : ℕ) : ℝ) ≤
        affineSup f (16 * M) ∧
      ∀ k ∈ range 4, affineEnergy f (((2 ^ k * M : ℕ) : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2)
        ((2 * M₁ : ℕ) : ℝ) ≤ affineSup f (16 * M) := by
  have h1 : (1 : ℝ) ≤ M₁ := by exact_mod_cast hM₁
  have h2 : (M₁ : ℝ) ≤ M := by exact_mod_cast hM₁M
  refine ⟨affineEnergy_le_affineSup hf hfc ⟨by linarith, by linarith, by linarith, by linarith,
    by push_cast; linarith, by push_cast; linarith⟩, fun k hk => ?_⟩
  have hk4 : k < 4 := Finset.mem_range.mp hk
  have hpow : (2 : ℝ) ^ k ≤ 8 := by
    have : (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [show (2 : ℝ) ^ 3 = 8 by norm_num]
  have hpow1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  refine affineEnergy_le_affineSup hf hfc ⟨?_, ?_, by linarith, by linarith, by push_cast; linarith,
    by push_cast; linarith⟩
  · push_cast
    nlinarith
  · push_cast
    nlinarith

end

end RHTower.GuthMaynard
