import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexUnderRotationDampingAndCoalescence

/-!
# The index of a Bohr series

The covariant classification for kernels whose spectrum lies on the unitary dual, with infinite
support. A **Bohr series** on an abelian group is `k = Σ_j a_j ψ_j`, with distinct unitary
characters `ψ_j` and absolutely summable real coefficients. On `ℚ_{>0}` the on-line part of the
Weil kernel is of this form, with `ψ_γ(u) = u^{iγ}`.

**The Toeplitz form** (`hermQuad_gram_bohrSum`). On every family the form of `k` is
`Σ_j a_j |Σ_b c_b ψ_j(x_b)|²`.

**The index** (`negIndex_bohrSum`). `κ(k)` is the number of negative coefficients. The upper bound
holds because the form is nonnegative on the common kernel of the evaluations at the negative
characters. For the lower bound, average over boxes `{Π_k g_k^{e_k}}`, where each `g_k` separates
two of the characters. The Bohr means of `conj ψ_i · ψ_j` tend to `δ_ij`, so on the span of the
averaged conjugates of the negative characters the form converges entrywise, by dominated
convergence, to the negative diagonal of their coefficients. It is then eventually negative
definite.

So a Bohr series has finite index iff only finitely many coefficients are negative. In that case it
is a positive-definite Bohr series minus finitely many characters, which is the Krein–Langer
structure in this class, with no separation hypothesis.
-/

open Complex Finset Filter Topology Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (negIndex_le_card_of_nonneg_on_ker)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [CommGroup G]

/-- A **Bohr series** `Σ_j a_j ψ_j` of characters with real coefficients. -/
def bohrSum (ψ : ℕ → G →* ℂ) (a : ℕ → ℝ) (u : G) : ℂ := ∑' j, (a j : ℂ) * ψ j u

section Form

variable {ψ : ℕ → G →* ℂ} (hψ : ∀ j, IsUnitaryChar (ψ j)) {a : ℕ → ℝ} (ha : Summable a)

include ha in
theorem summable_coeff_mul {f : ℕ → ℂ} {C : ℝ} (hf : ∀ j, ‖f j‖ ≤ C) :
    Summable fun j => (a j : ℂ) * f j :=
  Summable.of_norm_bounded ((summable_abs_iff.mpr ha).mul_right C) fun j => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf j) (abs_nonneg _)

include hψ in
theorem unitary_inv_mul (j : ℕ) (u v : G) : ψ j (u⁻¹ * v) = conj (ψ j u) * ψ j v := by
  rw [map_mul, map_inv_eq_inv, inv_eq_conj_of_unitary (hψ j)]

include hψ in
theorem norm_charEval_le {ι : Type*} [Fintype ι] (x : ι → G) (c : ι → ℂ) (j : ℕ) :
    ‖charEval (ψ j) x c‖ ≤ ∑ b, ‖c b‖ := by
  rw [charEval_apply]
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun b _ => ?_))
  rw [norm_mul, hψ j, mul_one]

include hψ ha in
/-- **The Toeplitz form of a Bohr series** is `Σ_j a_j |Σ_b c_b ψ_j(x_b)|²`. -/
theorem hermQuad_gram_bohrSum {ι : Type*} [Fintype ι] (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram (bohrSum ψ a) x) c = ∑' j, a j * normSq (charEval (ψ j) x c) := by
  have hentry : ∀ p q, conj (c p) * bohrSum ψ a ((x p)⁻¹ * x q) * c q =
      ∑' j, conj (c p) * ((a j : ℂ) * ψ j ((x p)⁻¹ * x q)) * c q := fun p q => by
    rw [bohrSum, ← tsum_mul_left, ← tsum_mul_right]
  have hsumm : ∀ p q, Summable fun j => conj (c p) * ((a j : ℂ) * ψ j ((x p)⁻¹ * x q)) * c q :=
    fun p q => by
      have := (summable_coeff_mul ha (f := fun j => ψ j ((x p)⁻¹ * x q)) (C := 1)
        fun j => (hψ j _).le).mul_left (conj (c p))
      exact this.mul_right (c q)
  have hterm : ∀ j, ∑ p, ∑ q, conj (c p) * ((a j : ℂ) * ψ j ((x p)⁻¹ * x q)) * c q =
      ((a j * normSq (charEval (ψ j) x c) : ℝ) : ℂ) := fun j => by
    push_cast
    rw [normSq_eq_conj_mul_self, charEval_apply, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun q _ => ?_
    rw [unitary_inv_mul hψ, map_mul]
    ring
  have hswap : ∑ p, ∑ q, conj (c p) * bohrSum ψ a ((x p)⁻¹ * x q) * c q =
      ∑' j, ∑ p, ∑ q, conj (c p) * ((a j : ℂ) * ψ j ((x p)⁻¹ * x q)) * c q := by
    rw [Summable.tsum_finsetSum fun p _ => summable_sum fun q _ => hsumm p q]
    refine sum_congr rfl fun p _ => ?_
    rw [Summable.tsum_finsetSum fun q _ => hsumm p q]
    exact sum_congr rfl fun q _ => hentry p q
  rw [hermQuad_gram, hswap, tsum_congr hterm, ← ofReal_tsum, ofReal_re]

include hψ ha in
/-- At most one negative square per negative coefficient. -/
theorem negIndex_bohrSum_le : negIndex (bohrSum ψ a) ≤ {j | a j < 0}.encard := by
  classical
  rcases Set.finite_or_infinite {j | a j < 0} with hfin | hinf
  · rw [hfin.encard_eq_coe_toFinset_card]
    refine negIndex_le_iff.mpr fun n x => ?_
    have h := negIndex_le_card_of_nonneg_on_ker (gram (bohrSum ψ a) x)
      (fun j : hfin.toFinset => charEval (ψ j) x) fun c hc => by
        rw [hermQuad_gram_bohrSum hψ ha]
        refine tsum_nonneg fun j => ?_
        by_cases hj : a j < 0
        · rw [hc ⟨j, hfin.mem_toFinset.mpr hj⟩]
          simp
        · exact mul_nonneg (not_lt.mp hj) (normSq_nonneg _)
    rw [Fintype.card_coe] at h
    exact_mod_cast h
  · rw [hinf.encard_eq]
    exact le_top

end Form

/-! ### Bohr means over boxes -/

section Box

variable (ψ : ℕ → G →* ℂ)

open Classical in
/-- A point where `ψ i` and `ψ j` differ, when they do. -/
def sepPair (i j : ℕ) : G := if h : ∃ g, ψ i g ≠ ψ j g then h.choose else 1

/-- The separating point for the pair coded by `k`. -/
def sepPoint (k : ℕ) : G := sepPair ψ (Nat.unpair k).1 (Nat.unpair k).2

theorem sepPoint_pair_spec (hinj : Function.Injective ψ) {i j : ℕ} (hij : i ≠ j) :
    ψ i (sepPoint ψ (Nat.pair i j)) ≠ ψ j (sepPoint ψ (Nat.pair i j)) := by
  have hex : ∃ g, ψ i g ≠ ψ j g := by
    by_contra h
    push Not at h
    exact hij (hinj (MonoidHom.ext h))
  rw [sepPoint, Nat.unpair_pair]
  simp only
  rw [sepPair, dif_pos hex]
  exact hex.choose_spec

/-- The box `{Π_{k<T} g_k^{e_k} : 0 ≤ e_k < T}`, as a family. -/
def boxPoint (T : ℕ) (e : Fin T → Fin T) : G := ∏ k : Fin T, sepPoint ψ k ^ (e k : ℕ)

/-- The Bohr mean of `conj ψ_i · ψ_j` over the box of size `T`. -/
def boxMean (T i j : ℕ) : ℂ :=
  ((T : ℂ) ^ T)⁻¹ * ∑ e : Fin T → Fin T, conj (ψ i (boxPoint ψ T e)) * ψ j (boxPoint ψ T e)

/-- The box mean is a product of one-generator means. -/
theorem boxMean_eq (T i j : ℕ) : boxMean ψ T i j = ∏ k : Fin T, ((T : ℂ)⁻¹ *
    ∑ n : Fin T, (conj (ψ i (sepPoint ψ k)) * ψ j (sepPoint ψ k)) ^ (n : ℕ)) := by
  have hpt : ∀ e : Fin T → Fin T, conj (ψ i (boxPoint ψ T e)) * ψ j (boxPoint ψ T e) =
      ∏ k : Fin T, (conj (ψ i (sepPoint ψ k)) * ψ j (sepPoint ψ k)) ^ (e k : ℕ) := fun e => by
    simp only [boxPoint, map_prod, map_pow]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => (mul_pow _ _ _).symm
  simp only [boxMean, hpt]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
    Fintype.prod_sum]

variable {ψ} (hψ : ∀ j, IsUnitaryChar (ψ j))

omit hψ in
theorem norm_avg_le_one {z : ℂ} (hz : ‖z‖ = 1) {T : ℕ} (hT : 0 < T) :
    ‖(T : ℂ)⁻¹ * ∑ n : Fin T, z ^ (n : ℕ)‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h : ‖∑ n : Fin T, z ^ (n : ℕ)‖ ≤ T := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_pow, hz]
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  calc (T : ℝ)⁻¹ * ‖∑ n : Fin T, z ^ (n : ℕ)‖ ≤ (T : ℝ)⁻¹ * T :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 := inv_mul_cancel₀ hT'.ne'

omit hψ in
theorem norm_avg_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {T : ℕ} (hT : 0 < T) :
    ‖(T : ℂ)⁻¹ * ∑ n : Fin T, z ^ (n : ℕ)‖ ≤ 2 / (T * ‖1 - z‖) := by
  have hne : ‖1 - z‖ ≠ 0 := by rw [norm_ne_zero_iff, sub_ne_zero]; exact Ne.symm hz1
  have hpos : 0 < ‖1 - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  rw [Fin.sum_univ_eq_sum_range (fun n => z ^ n) T, geom_sum_eq hz1, norm_mul, norm_inv,
    Complex.norm_natCast, norm_div, ← norm_neg (z - 1), neg_sub]
  have hnum : ‖z ^ T - 1‖ ≤ 2 := by
    calc ‖z ^ T - 1‖ ≤ ‖z ^ T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  rw [div_eq_mul_inv, ← mul_assoc, mul_comm (T : ℝ)⁻¹, mul_assoc, ← mul_inv, mul_comm (T : ℝ)]
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hnum (by positivity)

include hψ in
theorem norm_boxMean_le_one {T : ℕ} (hT : 0 < T) (i j : ℕ) : ‖boxMean ψ T i j‖ ≤ 1 := by
  rw [boxMean_eq, norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => norm_avg_le_one ?_ hT
  rw [norm_mul, Complex.norm_conj, hψ i, hψ j, one_mul]

include hψ in
theorem boxMean_self (T i : ℕ) : boxMean ψ T i i = 1 := by
  rw [boxMean_eq]
  refine Finset.prod_eq_one fun k _ => ?_
  have hT : (T : ℂ) ≠ 0 := by
    have : 0 < T := Fin.pos k
    exact_mod_cast this.ne'
  have h1 : conj (ψ i (sepPoint ψ k)) * ψ i (sepPoint ψ k) = 1 := by
    rw [← inv_eq_conj_of_unitary (hψ i), inv_mul_cancel₀ (map_ne_zero (ψ i) _)]
  simp only [h1, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  exact inv_mul_cancel₀ hT

include hψ in
/-- **Bohr means separate characters**: the box means of `conj ψ_i · ψ_j` tend to `δ_ij`. -/
theorem tendsto_boxMean (hinj : Function.Injective ψ) (i j : ℕ) :
    Tendsto (fun T => boxMean ψ T i j) atTop (𝓝 (if i = j then 1 else 0)) := by
  by_cases hij : i = j
  · subst hij
    simp only [if_true, boxMean_self hψ]
    exact tendsto_const_nhds
  rw [if_neg hij]
  set g := sepPoint ψ (Nat.pair i j)
  set z := conj (ψ i g) * ψ j g
  have hz : ‖z‖ = 1 := by rw [norm_mul, Complex.norm_conj, hψ i, hψ j, one_mul]
  have hz1 : z ≠ 1 := fun h => by
    apply sepPoint_pair_spec ψ hinj hij
    have h2 : conj (ψ i g) * ψ i g = 1 := by
      rw [← inv_eq_conj_of_unitary (hψ i), inv_mul_cancel₀ (map_ne_zero (ψ i) _)]
    have hne : conj (ψ i g) ≠ 0 := star_ne_zero.mpr (map_ne_zero (ψ i) _)
    exact mul_left_cancel₀ hne (h2.trans h.symm)
  have hpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hbound : ∀ᶠ T in atTop, ‖boxMean ψ T i j‖ ≤ 2 / ‖1 - z‖ * (T : ℝ)⁻¹ := by
    filter_upwards [eventually_gt_atTop (Nat.pair i j)] with T hT
    have hT0 : 0 < T := lt_of_le_of_lt (Nat.zero_le _) hT
    set k₀ : Fin T := ⟨Nat.pair i j, hT⟩
    rw [boxMean_eq, norm_prod, ← Finset.mul_prod_erase _ _ (mem_univ k₀)]
    have hrest : ∏ k ∈ univ.erase k₀, ‖(T : ℂ)⁻¹ * ∑ n : Fin T,
        (conj (ψ i (sepPoint ψ k)) * ψ j (sepPoint ψ k)) ^ (n : ℕ)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => norm_avg_le_one
        (by rw [norm_mul, Complex.norm_conj, hψ i, hψ j, one_mul]) hT0
    have hk₀ := norm_avg_le hz hz1 hT0
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
    calc _ ≤ ‖(T : ℂ)⁻¹ * ∑ n : Fin T, z ^ (n : ℕ)‖ * 1 :=
          mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
      _ ≤ 2 / (T * ‖1 - z‖) := by rw [mul_one]; exact hk₀
      _ = 2 / ‖1 - z‖ * (T : ℝ)⁻¹ := by field_simp
  have hlim : Tendsto (fun T : ℕ => 2 / ‖1 - z‖ * (T : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 / ‖1 - z‖)
  exact squeeze_zero_norm' hbound hlim

end Box

/-! ### The lower bound -/

section Lower

variable {ψ : ℕ → G →* ℂ} (hψ : ∀ j, IsUnitaryChar (ψ j)) {a : ℕ → ℝ} (ha : Summable a)

include hψ ha in
/-- **Negative coefficients give negative squares.** Any `r` negative coefficients give `r`
negative squares. -/
theorem le_negIndex_bohrSum (hinj : Function.Injective ψ) {r : ℕ} {t : Fin r → ℕ}
    (ht : Function.Injective t) (hneg : ∀ i, a (t i) < 0) : (r : ℕ∞) ≤ negIndex (bohrSum ψ a) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image univ (fun i => -a (t i))
    (univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩)
  set δ := -a (t i₀)
  have hδ : 0 < δ := by linarith [hneg i₀]
  have hδle : ∀ i, a (t i) ≤ -δ := fun i => by linarith [hi₀ i (mem_univ _)]
  -- the compressed forms on the averaged conjugates of the negative characters
  set A : ℕ → Matrix (Fin r) (Fin r) ℂ := fun T i l =>
    ∑' j, (a j : ℂ) * (conj (boxMean ψ T (t i) j) * boxMean ψ T (t l) j)
  have hlim : ∀ i l, Tendsto (fun T => A T i l) atTop
      (𝓝 (diagonal (fun i => ((a (t i) : ℝ) : ℂ)) i l)) := fun i l => by
    have hg : ∀ j, Tendsto (fun T => (a j : ℂ) * (conj (boxMean ψ T (t i) j) *
        boxMean ψ T (t l) j)) atTop (𝓝 ((a j : ℂ) * (conj (if t i = j then (1 : ℂ) else 0) *
          (if t l = j then 1 else 0)))) := fun j =>
      tendsto_const_nhds.mul (((Complex.continuous_conj.tendsto _).comp
        (tendsto_boxMean hψ hinj (t i) j)).mul (tendsto_boxMean hψ hinj (t l) j))
    have hb : ∀ᶠ T in atTop, ∀ j, ‖(a j : ℂ) * (conj (boxMean ψ T (t i) j) *
        boxMean ψ T (t l) j)‖ ≤ |a j| := by
      filter_upwards [eventually_ge_atTop 1] with T hT j
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      have h1 := norm_boxMean_le_one hψ hT (t i) j
      have h2 := norm_boxMean_le_one hψ hT (t l) j
      calc |a j| * (‖boxMean ψ T (t i) j‖ * ‖boxMean ψ T (t l) j‖) ≤ |a j| * (1 * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one)
              (abs_nonneg _)
        _ = |a j| := by ring
    have h := tendsto_tsum_of_dominated_convergence (summable_abs_iff.mpr ha) hg hb
    convert h using 2
    by_cases hil : i = l
    · subst hil
      rw [diagonal_apply_eq]
      rw [tsum_eq_single (t i) fun j hj => by simp [Ne.symm hj]]
      simp
    · rw [diagonal_apply_ne _ hil]
      symm
      refine (tsum_congr fun j => ?_).trans tsum_zero
      by_cases h1 : t i = j
      · have h2 : t l ≠ j := fun h => hil (ht (h1.trans h.symm))
        simp [h1, h2]
      · simp [h1]
  have hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop, ∀ i l,
      ‖A T i l - diagonal (fun i => ((a (t i) : ℝ) : ℂ)) i l‖ ≤ ε := fun ε hε => by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro l
    filter_upwards [(Metric.tendsto_nhds.mp (hlim i l)) ε hε] with T hT
    rw [← dist_eq_norm]
    exact hT.le
  obtain ⟨T, hT⟩ := (eventually_negDef_of_entrywise_tendsto_diagonal A (fun i => a (t i)) hδ hδle
    hconv).exists
  -- the averaged conjugates of the negative characters
  set x : (Fin T → Fin T) → G := boxPoint ψ T
  set L : (Fin r → ℂ) →ₗ[ℂ] ((Fin T → Fin T) → ℂ) := Fintype.linearCombination ℂ
    fun i e => ((T : ℂ) ^ T)⁻¹ * conj (ψ (t i) (x e))
  have hE : ∀ β j, charEval (ψ j) x (L β) = ∑ i, β i * boxMean ψ T (t i) j := fun β j => by
    simp only [charEval_apply, L, Fintype.linearCombination_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, boxMean, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun e _ => ?_
    ring
  have hsA : ∀ i l, Summable fun j =>
      (a j : ℂ) * (conj (boxMean ψ T (t i) j) * boxMean ψ T (t l) j) := fun i l => by
    rcases Nat.eq_zero_or_pos T with hT0 | hT0
    · subst hT0
      exact summable_coeff_mul ha (C := 1) fun j => by
        simp [boxMean, boxPoint]
    · exact summable_coeff_mul ha (C := 1) fun j => by
        rw [norm_mul, Complex.norm_conj]
        exact (mul_le_mul (norm_boxMean_le_one hψ hT0 _ _) (norm_boxMean_le_one hψ hT0 _ _)
          (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hform : ∀ β, hermQuad (gram (bohrSum ψ a) x) (L β) = (star β ⬝ᵥ A T *ᵥ β).re := fun β => by
    rw [hermQuad_gram_bohrSum hψ ha]
    simp only [hE]
    have hc : (star β ⬝ᵥ A T *ᵥ β) = ∑' j, ((a j * normSq (∑ i, β i * boxMean ψ T (t i) j) : ℝ) :
        ℂ) := by
      simp only [dotProduct, mulVec, A, Pi.star_apply, RCLike.star_def]
      have hin : ∀ i, conj (β i) * ∑ l, (∑' j, (a j : ℂ) *
          (conj (boxMean ψ T (t i) j) * boxMean ψ T (t l) j)) * β l =
          ∑' j, ∑ l, conj (β i) * ((a j : ℂ) *
            (conj (boxMean ψ T (t i) j) * boxMean ψ T (t l) j)) * β l := fun i => by
        rw [Summable.tsum_finsetSum fun l _ => ((hsA i l).mul_left _).mul_right _, Finset.mul_sum]
        refine sum_congr rfl fun l _ => ?_
        rw [← tsum_mul_right, ← tsum_mul_left]
        exact tsum_congr fun j => by ring
      simp only [hin]
      rw [← Summable.tsum_finsetSum fun i _ => summable_sum fun l _ =>
        ((hsA i l).mul_left _).mul_right _]
      refine tsum_congr fun j => ?_
      push_cast
      rw [normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [map_mul]
      ring
    rw [hc, ← ofReal_tsum, ofReal_re]
  have h := card_le_hermNegIndex_of_forall_neg (gram (bohrSum ψ a) x) L fun β hβ => by
    rw [hform]
    exact hT β hβ
  rw [Fintype.card_fin] at h
  exact (Nat.cast_le.mpr h).trans (hermNegIndex_gram_le_negIndex _ x)

include hψ ha in
/-- **The index of a Bohr series is its number of negative coefficients.** -/
theorem negIndex_bohrSum (hinj : Function.Injective ψ) :
    negIndex (bohrSum ψ a) = {j | a j < 0}.encard := by
  refine le_antisymm (negIndex_bohrSum_le hψ ha) ?_
  rcases Set.finite_or_infinite {j | a j < 0} with hfin | hinf
  · rw [hfin.encard_eq_coe_toFinset_card]
    set S := hfin.toFinset
    exact le_negIndex_bohrSum hψ ha hinj (t := fun i => (S.equivFin.symm i : ℕ))
      (fun i i' h => S.equivFin.symm.injective (Subtype.ext h))
      fun i => hfin.mem_toFinset.mp (S.equivFin.symm i).2
  · rw [hinf.encard_eq, top_le_iff, ENat.eq_top_iff_forall_ge]
    intro m
    obtain ⟨S, hS, hcard⟩ := hinf.exists_subset_card_eq m
    have h := le_negIndex_bohrSum hψ ha hinj (t := fun i => (S.equivFin.symm i : ℕ))
      (fun i i' h => S.equivFin.symm.injective (Subtype.ext h))
      fun i => hS (S.equivFin.symm i).2
    rwa [hcard] at h

include hψ ha in
/-- **Finite index is finitely many negative coefficients.** -/
theorem negIndex_bohrSum_lt_top_iff (hinj : Function.Injective ψ) :
    negIndex (bohrSum ψ a) < ⊤ ↔ {j | a j < 0}.Finite := by
  rw [negIndex_bohrSum hψ ha hinj, Set.encard_lt_top_iff]

end Lower

end GaloisForLFunctions.HeckeKreinToeplitz
