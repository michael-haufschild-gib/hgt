import GaloisForLFunctions.RHTower.Sieve.GuthMaynardAffineSum
import GaloisForLFunctions.RHTower.Sieve.PhaseGeometricBound
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation
import GaloisForLFunctions.HTGeometry.FourierDecayFromDerivative

set_option autoImplicit false

/-!
# The Fejér majorant of an affine sum and its Fourier transform

Fix `f ≥ 0` continuous with compact support and put `ψ(x) = Σ_{m ∼ M₂} f(x/m)`, so that the
positive affine sum is `A₊(u) = Σ_{n ∼ M₁} Σ_{|h| ≤ M₃} ψ(n u + h)`. Every `|h| ≤ M₃` is a
difference `a − b` with `a, b < 2L` in at least `L = ⌊M₃⌋ + 1` ways, hence
(`posAffineSum_le_fejerMajorant`)

`L · A₊(u) ≤ G(u) = Σ_{n ∼ M₁} Σ_{a, b < K} ψ(n u + a − b)`,  `K = 2L`.

The Fejér weights make the Fourier transform factorise exactly. With `χ(x) = Σ_{a<K} ψ(x + a)` and
`D_K(θ) = Σ_{a<K} e(aθ)`:

* `ψ̂(θ) = Σ_m m f̂(mθ)` (`fourier_dilationSum`);
* `χ̂(θ) = D_K(θ) ψ̂(θ)` (`fourier_translateSum`);
* `Ĝ(ξ) = Σ_{n ∼ M₁} n⁻¹ \overline{D_K(ξ/n)} χ̂(ξ/n)` (`fourier_fejerMajorant`).

The square function of `χ` is an affine sum one level down (`integral_translateSum_sq_le`):

`∫ χ² ≤ 2 K M₂ ∫ f(u) A₊'(u) du`,  `A₊'` the positive affine sum at scales `(M₂, M₂, K − 1)`,

by translating, bounding `Σ_b ψ(y − a + b) ≤ Σ_{|h| < K} ψ(y + h)`, and substituting `y = m' u`.
-/

open MeasureTheory Finset Complex
open scoped FourierTransform ComplexConjugate

namespace RHTower.GuthMaynard

noncomputable section

open RHTower.Sieve (finitePhaseChar finitePhaseProgression)

/-- `ψ(x) = Σ_{m ∼ M₂} f(x/m)`. -/
def dilationSum (f : ℝ → ℝ) (M₂ x : ℝ) : ℝ :=
  ∑ m ∈ dyadicNat M₂, f (x / m)

/-- `χ(x) = Σ_{0 ≤ a < K} ψ(x + a)`. -/
def translateSum (f : ℝ → ℝ) (M₂ : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ range K, dilationSum f M₂ (x + a)

/-- The Fejér majorant `G(u) = Σ_{n ∼ M₁} Σ_{0 ≤ b < K} χ(n u − b)`. -/
def fejerMajorant (f : ℝ → ℝ) (M₁ M₂ : ℝ) (K : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ dyadicNat M₁, ∑ b ∈ range K, translateSum f M₂ K (n * u - b)

/-- A real function viewed as a complex one. -/
def complexify (g : ℝ → ℝ) : ℝ → ℂ := fun x => (g x : ℂ)

theorem dilationSum_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (M₂ x : ℝ) : 0 ≤ dilationSum f M₂ x :=
  Finset.sum_nonneg fun _ _ => hf0 _

theorem translateSum_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (M₂ : ℝ) (K : ℕ) (x : ℝ) :
    0 ≤ translateSum f M₂ K x :=
  Finset.sum_nonneg fun _ _ => dilationSum_nonneg hf0 _ _

theorem fejerMajorant_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (M₁ M₂ : ℝ) (K : ℕ) (u : ℝ) :
    0 ≤ fejerMajorant f M₁ M₂ K u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => translateSum_nonneg hf0 _ _ _

/-! ### Counting differences -/

/-- Every `|h| ≤ M₃` is `a − b` with `a, b < 2L` in at least `L = ⌊M₃⌋₊ + 1` ways. -/
theorem card_mul_sum_centredInt_le_sum_sub {F : ℤ → ℝ} (hF : ∀ h, 0 ≤ F h) {M₃ : ℝ}
    (hM₃ : 0 ≤ M₃) :
    ((⌊M₃⌋₊ + 1 : ℕ) : ℝ) * ∑ h ∈ centredInt M₃, F h ≤
      ∑ a ∈ range (2 * (⌊M₃⌋₊ + 1)), ∑ b ∈ range (2 * (⌊M₃⌋₊ + 1)), F ((a : ℤ) - b) := by
  set L := ⌊M₃⌋₊ + 1 with hL
  let φ : ℕ × ℤ → ℕ × ℕ := fun p => (p.1 + p.2.toNat, p.1 + (-p.2).toNat)
  have hhb : ∀ h ∈ centredInt M₃, h.toNat ≤ ⌊M₃⌋₊ ∧ (-h).toNat ≤ ⌊M₃⌋₊ := fun h hh => by
    have h1 := abs_le.mp (mem_centredInt.mp hh)
    have h2 : h ≤ ⌊M₃⌋ := Int.le_floor.mpr h1.2
    have h3 : -h ≤ ⌊M₃⌋ := Int.le_floor.mpr (by push_cast; linarith [h1.1])
    rw [← Int.natCast_floor_eq_floor hM₃] at h2 h3
    exact ⟨Int.toNat_le.mpr h2, Int.toNat_le.mpr h3⟩
  have hinj : Set.InjOn φ ↑(range L ×ˢ centredInt M₃) := by
    rintro ⟨c, h⟩ - ⟨c', h'⟩ - hp
    simp only [φ, Prod.mk.injEq] at hp
    obtain ⟨h1, h2⟩ := hp
    have e1 := Int.toNat_sub_toNat_neg h
    have e2 := Int.toNat_sub_toNat_neg h'
    have h1' : (c : ℤ) + h.toNat = c' + h'.toNat := by exact_mod_cast h1
    have h2' : (c : ℤ) + (-h).toNat = c' + (-h').toNat := by exact_mod_cast h2
    have hh : h = h' := by linarith
    subst hh
    simp only [Prod.mk.injEq, and_true]
    omega
  have himage : (range L ×ˢ centredInt M₃).image φ ⊆ range (2 * L) ×ˢ range (2 * L) := by
    intro q hq
    obtain ⟨⟨c, h⟩, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hc, hh⟩ := Finset.mem_product.mp hp
    have hc' := Finset.mem_range.mp hc
    obtain ⟨t1, t2⟩ := hhb h hh
    simp only [φ, Finset.mem_product, Finset.mem_range]
    constructor <;> omega
  calc ((L : ℕ) : ℝ) * ∑ h ∈ centredInt M₃, F h
      = ∑ p ∈ range L ×ˢ centredInt M₃, F p.2 := by
        simp only [Finset.sum_product, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ∑ p ∈ range L ×ˢ centredInt M₃, F (((φ p).1 : ℤ) - (φ p).2) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        have := Int.toNat_sub_toNat_neg p.2
        simp only [φ]
        push_cast
        linarith
    _ = ∑ q ∈ (range L ×ˢ centredInt M₃).image φ, F ((q.1 : ℤ) - q.2) :=
        (Finset.sum_image (f := fun q : ℕ × ℕ => F ((q.1 : ℤ) - q.2)) hinj).symm
    _ ≤ ∑ q ∈ range (2 * L) ×ˢ range (2 * L), F ((q.1 : ℤ) - q.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg himage fun q _ _ => hF _
    _ = _ := Finset.sum_product _ _ _

/-- For `a < K` the shifts `b − a` (`b < K`) are distinct integers with `|b − a| ≤ K − 1`. -/
theorem sum_range_sub_le_sum_centredInt {F : ℤ → ℝ} (hF : ∀ h, 0 ≤ F h) {K a : ℕ} (ha : a < K) :
    ∑ b ∈ range K, F ((b : ℤ) - a) ≤ ∑ h ∈ centredInt ((K : ℝ) - 1), F h := by
  have hinj : Set.InjOn (fun b : ℕ => (b : ℤ) - a) ↑(range K) := fun b _ b' _ h => by
    simp only at h
    omega
  have hsub : (range K).image (fun b : ℕ => (b : ℤ) - a) ⊆ centredInt ((K : ℝ) - 1) := by
    intro h hh
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
    have hb' : (b : ℝ) + 1 ≤ K := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hb)
    have ha' : (a : ℝ) + 1 ≤ K := by exact_mod_cast Nat.succ_le_of_lt ha
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    rw [mem_centredInt, abs_le]
    push_cast
    constructor <;> linarith
  calc ∑ b ∈ range K, F ((b : ℤ) - a)
      = ∑ h ∈ (range K).image (fun b : ℕ => (b : ℤ) - a), F h := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hF _

/-- **The Fejér majorant.** `L · A₊ ≤ G` with `L = ⌊M₃⌋₊ + 1`, `K = 2L`. -/
theorem posAffineSum_le_fejerMajorant {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (M₁ M₂ : ℝ) {M₃ : ℝ}
    (hM₃ : 0 ≤ M₃) (u : ℝ) :
    ((⌊M₃⌋₊ + 1 : ℕ) : ℝ) * posAffineSum f M₁ M₂ M₃ u ≤
      fejerMajorant f M₁ M₂ (2 * (⌊M₃⌋₊ + 1)) u := by
  rw [posAffineSum, fejerMajorant, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hswap : ∑ m₂ ∈ dyadicNat M₂, ∑ m₃ ∈ centredInt M₃, f ((n * u + m₃) / m₂) =
      ∑ h ∈ centredInt M₃, dilationSum f M₂ (n * u + h) := by
    rw [Finset.sum_comm]
    rfl
  have hrhs : ∑ b ∈ range (2 * (⌊M₃⌋₊ + 1)), translateSum f M₂ (2 * (⌊M₃⌋₊ + 1)) (n * u - b) =
      ∑ a ∈ range (2 * (⌊M₃⌋₊ + 1)), ∑ b ∈ range (2 * (⌊M₃⌋₊ + 1)),
        dilationSum f M₂ (n * u + (((a : ℤ) - b : ℤ) : ℝ)) := by
    unfold translateSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    push_cast
    ring
  rw [hswap, hrhs]
  exact card_mul_sum_centredInt_le_sum_sub (F := fun h => dilationSum f M₂ (n * u + h))
    (fun h => dilationSum_nonneg hf0 _ _) hM₃

/-! ### Integrability -/

theorem memLp_dilationSum_affine {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₂ : ℝ) {n : ℝ} (hn : n ≠ 0) (c : ℝ) (p : ENNReal) :
    MemLp (fun u => dilationSum f M₂ (n * u + c)) p :=
  memLp_finsetSum _ fun m hm => memLp_affine_term hf hfc hn
    (Nat.cast_ne_zero.mpr (by have := one_le_of_mem_dyadicNat hm; omega)) c p

theorem memLp_translateSum_affine {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₂ : ℝ) (K : ℕ) {n : ℝ} (hn : n ≠ 0) (c : ℝ) (p : ENNReal) :
    MemLp (fun u => translateSum f M₂ K (n * u + c)) p := by
  have h : (fun u => translateSum f M₂ K (n * u + c)) =
      fun u => ∑ a ∈ range K, dilationSum f M₂ (n * u + (c + a)) := by
    funext u
    unfold translateSum
    exact Finset.sum_congr rfl fun a _ => by rw [add_assoc]
  rw [h]
  exact memLp_finsetSum _ fun a _ => memLp_dilationSum_affine hf hfc M₂ hn _ p

theorem memLp_dilationSum {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₂ : ℝ) (p : ENNReal) : MemLp (dilationSum f M₂) p := by
  simpa using memLp_dilationSum_affine hf hfc M₂ one_ne_zero 0 p

theorem memLp_translateSum {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₂ : ℝ) (K : ℕ) (p : ENNReal) : MemLp (translateSum f M₂ K) p := by
  simpa using memLp_translateSum_affine hf hfc M₂ K one_ne_zero 0 p

theorem memLp_fejerMajorant {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₁ M₂ : ℝ) (K : ℕ) (p : ENNReal) : MemLp (fejerMajorant f M₁ M₂ K) p := by
  have h : fejerMajorant f M₁ M₂ K =
      fun u => ∑ n ∈ dyadicNat M₁, ∑ b ∈ range K, translateSum f M₂ K (n * u + -(b : ℝ)) := by
    funext u
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun b _ => by rw [sub_eq_add_neg]
  rw [h]
  exact memLp_finsetSum _ fun n hn => memLp_finsetSum _ fun b _ =>
    memLp_translateSum_affine hf hfc M₂ K
      (Nat.cast_ne_zero.mpr (by have := one_le_of_mem_dyadicNat hn; omega)) _ p

theorem integrable_complexify {g : ℝ → ℝ} (hg : MemLp g 1) : Integrable (complexify g) :=
  (memLp_one_iff_integrable.mp hg).ofReal

theorem memLp_complexify {g : ℝ → ℝ} {p : ENNReal} (hg : MemLp g p) : MemLp (complexify g) p :=
  hg.ofReal

/-! ### Fourier transforms -/

/-- Finite additivity of the Fourier integral (from `HTGeometry.fourierIntegral_add`). -/
theorem fourier_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℂ}
    (hF : ∀ i ∈ s, Integrable (F i)) (ξ : ℝ) :
    𝓕 (fun x => ∑ i ∈ s, F i x) ξ = ∑ i ∈ s, 𝓕 (F i) ξ := by
  induction s using Finset.cons_induction with
  | empty => simp [Real.fourier_real_eq_integral_exp_smul]
  | cons i s hi ih =>
    have hs : ∀ j ∈ s, Integrable (F j) := fun j hj => hF j (Finset.mem_cons.mpr (Or.inr hj))
    simp only [Finset.sum_cons]
    rw [← ih hs]
    exact GaloisForLFunctions.HTGeometry.fourierIntegral_add (hF i (Finset.mem_cons_self i s))
      (integrable_finsetSum _ hs) ξ

/-- `ψ̂(θ) = Σ_{m ∼ M₂} m f̂(mθ)`. -/
theorem fourier_dilationSum {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₂ θ : ℝ) :
    𝓕 (complexify (dilationSum f M₂)) θ =
      ∑ m ∈ dyadicNat M₂, (m : ℂ) * 𝓕 (complexify f) (m * θ) := by
  have hfun : complexify (dilationSum f M₂) =
      fun x => ∑ m ∈ dyadicNat M₂, complexify (fun y => f (y / m)) x := by
    funext x
    simp [complexify, dilationSum]
  rw [hfun, fourier_sum]
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast one_le_of_mem_dyadicNat hm
    have := GaloisForLFunctions.HTGeometry.fourierIntegral_comp_div (complexify f) m hm0 θ
    rw [Complex.real_smul] at this
    exact this
  · intro m hm
    refine integrable_complexify ?_
    simpa using memLp_affine_term hf hfc one_ne_zero
      (Nat.cast_ne_zero.mpr (by have := one_le_of_mem_dyadicNat hm; omega)) 0 1

/-- `χ̂(θ) = D_K(θ) ψ̂(θ)`. -/
theorem fourier_translateSum {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₂ : ℝ) (K : ℕ) (θ : ℝ) :
    𝓕 (complexify (translateSum f M₂ K)) θ =
      finitePhaseProgression K θ * 𝓕 (complexify (dilationSum f M₂)) θ := by
  have hfun : complexify (translateSum f M₂ K) =
      fun x => ∑ a ∈ range K, complexify (dilationSum f M₂) (x + a) := by
    funext x
    simp [complexify, translateSum]
  rw [hfun, fourier_sum]
  · simp_rw [GaloisForLFunctions.HTGeometry.fourierIntegral_comp_add_right, smul_eq_mul]
    rw [← Finset.sum_mul, RHTower.Sieve.finitePhaseProgression,
      Fin.sum_univ_eq_sum_range (fun a => finitePhaseChar ((a : ℝ) * θ)) K]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold finitePhaseChar
    congr 2
    push_cast
    ring
  · intro a _
    refine integrable_complexify ?_
    simpa using memLp_dilationSum_affine hf hfc M₂ one_ne_zero (a : ℝ) 1

/-- `Ĝ(ξ) = Σ_{n ∼ M₁} n⁻¹ \overline{D_K(ξ/n)} χ̂(ξ/n)`. -/
theorem fourier_fejerMajorant {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₁ M₂ : ℝ) (K : ℕ) (ξ : ℝ) :
    𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ =
      ∑ n ∈ dyadicNat M₁, (n : ℂ)⁻¹ *
        (conj (finitePhaseProgression K (ξ / n)) * 𝓕 (complexify (translateSum f M₂ K)) (ξ / n)) := by
  set χC := complexify (translateSum f M₂ K) with hχC
  have hn0 : ∀ n ∈ dyadicNat M₁, (0 : ℝ) < n := fun n hn => by
    exact_mod_cast one_le_of_mem_dyadicNat hn
  have hterm : ∀ n ∈ dyadicNat M₁, ∀ b : ℕ,
      𝓕 (fun u => χC (n * u - b)) ξ =
        conj (finitePhaseChar (b * (ξ / n))) * ((n : ℂ)⁻¹ * 𝓕 χC (ξ / n)) := fun n hn b => by
    have hfun : (fun u : ℝ => χC (n * u - b)) = fun u => χC ((u - b / n) / (1 / n)) := by
      funext u
      congr 1
      field_simp [(hn0 n hn).ne']
    rw [hfun, GaloisForLFunctions.HTGeometry.fourierIntegral_comp_div_sub χC _ _
      (one_div_pos.mpr (hn0 n hn)) ξ, ← RHTower.Sieve.finitePhaseChar_neg, smul_eq_mul,
      Complex.real_smul]
    unfold finitePhaseChar
    congr 1
    · congr 2
      push_cast
      ring
    · push_cast
      ring_nf
  have hint : ∀ n ∈ dyadicNat M₁, ∀ b : ℕ, Integrable fun u => χC (n * u - b) := fun n hn b => by
    refine (integrable_complexify (memLp_translateSum_affine hf hfc M₂ K (hn0 n hn).ne'
      (-(b : ℝ)) 1)).congr (Filter.Eventually.of_forall fun u => ?_)
    rw [hχC]
    simp only [complexify, sub_eq_add_neg]
  have hfun : complexify (fejerMajorant f M₁ M₂ K) =
      fun u => ∑ n ∈ dyadicNat M₁, ∑ b ∈ range K, χC (n * u - b) := by
    funext u
    simp [χC, complexify, fejerMajorant]
  rw [hfun, fourier_sum _ fun n hn => integrable_finsetSum _ fun b _ => hint n hn b]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [fourier_sum _ fun b _ => hint n hn b]
  simp_rw [hterm n hn]
  rw [← Finset.sum_mul, RHTower.Sieve.finitePhaseProgression, map_sum,
    ← Fin.sum_univ_eq_sum_range (fun b => conj (finitePhaseChar ((b : ℝ) * (ξ / n)))) K]
  ring

/-! ### Norm bounds -/

/-- `‖f̂(η)‖ ≤ ∫ f` for `f ≥ 0` (`HTGeometry.norm_fourierReal_le_integral_norm`). -/
theorem norm_fourier_complexify_le {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (η : ℝ) :
    ‖𝓕 (complexify f) η‖ ≤ ∫ x, f x := by
  refine (GaloisForLFunctions.HTGeometry.norm_fourierReal_le_integral_norm _ η).trans
    (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)))
  simp [complexify, abs_of_nonneg (hf0 x)]

/-- `‖ψ̂(θ)‖ ≤ Σ_m m ‖f̂(mθ)‖`. -/
theorem norm_fourier_dilationSum_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₂ θ : ℝ) :
    ‖𝓕 (complexify (dilationSum f M₂)) θ‖ ≤
      ∑ m ∈ dyadicNat M₂, (m : ℝ) * ‖𝓕 (complexify f) (m * θ)‖ := by
  rw [fourier_dilationSum hf hfc]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ => ?_))
  rw [norm_mul, Complex.norm_natCast]

/-- `‖χ̂(θ)‖ = |D_K(θ)| ‖ψ̂(θ)‖`. -/
theorem norm_fourier_translateSum {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₂ : ℝ) (K : ℕ) (θ : ℝ) :
    ‖𝓕 (complexify (translateSum f M₂ K)) θ‖ =
      ‖finitePhaseProgression K θ‖ * ‖𝓕 (complexify (dilationSum f M₂)) θ‖ := by
  rw [fourier_translateSum hf hfc, norm_mul]

/-- `‖Ĝ(ξ)‖ ≤ Σ_n n⁻¹ |D_K(ξ/n)| ‖χ̂(ξ/n)‖`. -/
theorem norm_fourier_fejerMajorant_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₁ M₂ : ℝ) (K : ℕ) (ξ : ℝ) :
    ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ≤
      ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ * (‖finitePhaseProgression K (ξ / n)‖ *
        ‖𝓕 (complexify (translateSum f M₂ K)) (ξ / n)‖) := by
  rw [fourier_fejerMajorant hf hfc]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_inv, Complex.norm_natCast]

/-! ### The square function of `χ` -/

/-- **One level down.** `∫ χ² ≤ 2 K M₂ ∫ f · A₊'` with `A₊'` the positive affine sum at scales
`(M₂, M₂, K − 1)`. -/
theorem integral_translateSum_sq_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) (M₂ : ℝ) (K : ℕ) :
    ∫ x, translateSum f M₂ K x ^ 2 ≤
      K * (2 * M₂) * ∫ u, f u * posAffineSum f M₂ M₂ ((K : ℝ) - 1) u := by
  set ψ := dilationSum f M₂ with hψ
  set χ := translateSum f M₂ K with hχ
  set Φ : ℝ → ℝ := fun y => ∑ h ∈ centredInt ((K : ℝ) - 1), ψ (y + h) with hΦ
  have hψ0 : ∀ x, 0 ≤ ψ x := dilationSum_nonneg hf0 M₂
  have hΦ0 : ∀ y, 0 ≤ Φ y := fun y => Finset.sum_nonneg fun _ _ => hψ0 _
  have hΦL' : ∀ n : ℝ, n ≠ 0 → MemLp (fun u => Φ (n * u)) 2 := fun n hn =>
    memLp_finsetSum _ fun h _ => memLp_dilationSum_affine hf hfc M₂ hn (h : ℝ) 2
  have hψL : ∀ c : ℝ, MemLp (fun x => ψ (x + c)) 2 := fun c => by
    simpa using memLp_dilationSum_affine hf hfc M₂ one_ne_zero c 2
  have hψL0 : MemLp ψ 2 := memLp_dilationSum hf hfc M₂ 2
  have hχL0 : MemLp χ 2 := memLp_translateSum hf hfc M₂ K 2
  have hχL : ∀ c : ℝ, MemLp (fun x => χ (x - c)) 2 := fun c => by
    simpa [sub_eq_add_neg] using memLp_translateSum_affine hf hfc M₂ K one_ne_zero (-c) 2
  have hΦL1 : MemLp Φ 2 := by simpa using hΦL' 1 one_ne_zero
  have hfL : MemLp f 2 := hf.memLp_of_hasCompactSupport hfc
  -- `∫ χ² = Σ_a ∫ ψ(y) χ(y − a)`
  have hstep1 : ∫ x, χ x ^ 2 = ∑ a ∈ range K, ∫ y, ψ y * χ (y - a) := by
    have hpt : ∀ x, χ x ^ 2 = ∑ a ∈ range K, ψ (x + a) * χ x := fun x => by
      rw [sq, ← Finset.sum_mul]
      rfl
    have hint : ∀ a ∈ range K, Integrable fun x => ψ (x + a) * χ x := fun a _ =>
      (hψL (a : ℝ)).integrable_mul hχL0
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y => ψ y * χ (y - a)) (a : ℝ)
    simp only [add_sub_cancel_right] at this
    exact this
  -- `χ(y − a) ≤ Φ(y)`
  have hstep2 : ∀ a ∈ range K, ∫ y, ψ y * χ (y - a) ≤ ∫ y, ψ y * Φ y := fun a ha => by
    refine integral_mono ?_ ?_ fun y => mul_le_mul_of_nonneg_left ?_ (hψ0 y)
    · exact hψL0.integrable_mul (hχL (a : ℝ))
    · exact hψL0.integrable_mul hΦL1
    · have h := sum_range_sub_le_sum_centredInt (F := fun h => ψ (y + h)) (fun h => hψ0 _)
        (Finset.mem_range.mp ha)
      have hχy : χ (y - a) = ∑ b ∈ range K, ψ (y + (((b : ℤ) - a : ℤ) : ℝ)) := by
        rw [hχ, translateSum]
        refine Finset.sum_congr rfl fun b _ => ?_
        congr 1
        push_cast
        ring
      rw [hχy]
      exact h
  -- `∫ ψ Φ = Σ_{m'} m' ∫ f(u) Φ(m' u) du ≤ 2 M₂ ∫ f · A₊'`
  have hstep3 : ∫ y, ψ y * Φ y ≤ 2 * M₂ * ∫ u, f u * posAffineSum f M₂ M₂ ((K : ℝ) - 1) u := by
    have hm0 : ∀ m ∈ dyadicNat M₂, (0 : ℝ) < m := fun m hm => by
      exact_mod_cast one_le_of_mem_dyadicNat hm
    have hint1 : ∀ m ∈ dyadicNat M₂, Integrable fun y => f (y / m) * Φ y := fun m hm => by
      have hf' : MemLp (fun y => f (y / m)) 2 := by
        simpa using memLp_affine_term hf hfc one_ne_zero (hm0 m hm).ne' 0 2
      exact hf'.integrable_mul hΦL1
    have hint2 : ∀ m ∈ dyadicNat M₂, Integrable fun u => f u * Φ (m * u) := fun m hm =>
      hfL.integrable_mul (hΦL' m (hm0 m hm).ne')
    have hsub : ∀ m ∈ dyadicNat M₂, ∫ y, f (y / m) * Φ y = m * ∫ u, f u * Φ (m * u) :=
      fun m hm => by
        have h := Measure.integral_comp_mul_left (fun y => f (y / m) * Φ y) (m : ℝ)
        simp only [mul_div_cancel_left₀ _ (hm0 m hm).ne'] at h
        rw [h, smul_eq_mul, abs_inv, abs_of_pos (hm0 m hm), ← mul_assoc,
          mul_inv_cancel₀ (hm0 m hm).ne', one_mul]
    have hH : ∀ u, ∑ m ∈ dyadicNat M₂, Φ (m * u) = posAffineSum f M₂ M₂ ((K : ℝ) - 1) u :=
      fun u => by
        rw [posAffineSum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        rfl
    calc ∫ y, ψ y * Φ y = ∑ m ∈ dyadicNat M₂, ∫ y, f (y / m) * Φ y := by
          rw [← integral_finsetSum _ hint1]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show ψ y * Φ y = ∑ m ∈ dyadicNat M₂, f (y / m) * Φ y
          rw [← Finset.sum_mul]
          rfl
      _ = ∑ m ∈ dyadicNat M₂, (m : ℝ) * ∫ u, f u * Φ (m * u) := Finset.sum_congr rfl hsub
      _ ≤ ∑ m ∈ dyadicNat M₂, 2 * M₂ * ∫ u, f u * Φ (m * u) := by
          refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right
            (mem_dyadicNat.mp hm).2 (integral_nonneg fun u => mul_nonneg (hf0 u) (hΦ0 _))
      _ = 2 * M₂ * ∫ u, f u * posAffineSum f M₂ M₂ ((K : ℝ) - 1) u := by
          rw [← Finset.mul_sum, ← integral_finsetSum _ hint2]
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          show ∑ m ∈ dyadicNat M₂, f u * Φ (m * u) = f u * posAffineSum f M₂ M₂ ((K : ℝ) - 1) u
          rw [← hH u, Finset.mul_sum]
  have hI0 : 0 ≤ ∫ y, ψ y * Φ y := integral_nonneg fun y => mul_nonneg (hψ0 y) (hΦ0 y)
  calc ∫ x, χ x ^ 2 = ∑ a ∈ range K, ∫ y, ψ y * χ (y - a) := hstep1
    _ ≤ ∑ _a ∈ range K, ∫ y, ψ y * Φ y := Finset.sum_le_sum hstep2
    _ = K * ∫ y, ψ y * Φ y := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ K * (2 * M₂ * ∫ u, f u * posAffineSum f M₂ M₂ ((K : ℝ) - 1) u) := by gcongr
    _ = K * (2 * M₂) * ∫ u, f u * posAffineSum f M₂ M₂ ((K : ℝ) - 1) u := by ring

end

end RHTower.GuthMaynard
