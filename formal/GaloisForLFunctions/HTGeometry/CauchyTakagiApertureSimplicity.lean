import GaloisForLFunctions.HTGeometry.CauchyTakagiApertureBoundary

/-!
# Simplicity of the top Takagi value along the aperture flow

Keep the setting of `CauchyTakagiApertureBoundary`: distinct nodes `p_j` with positive real part,
the Gram matrix `H = [(p_j + p̄_k)⁻¹]`, profiles `w(s) = Σ_k y_k e^{−p̄_k s}` with `‖w‖² = y*Hy`,
masses `μ`, and the Takagi form `T_μ(y) = Σ_j μ_j ((Hy)_j)²`.

Let `Φ_μ(y) = conj(μ ∘ Hy)`. This con-linear map is `H`-symmetric, `⟨Φ_μ y, z⟩_H = Σ_j μ_j (Hy)_j (Hz)_j`,
so `T_μ(y) = ⟨Φ_μ y, y⟩_H`. A **Hermitian top vector** maximizes `R_μ(y)/‖y‖²_H` with
`R_μ(y) = ‖Φ_μ y‖²_H`.

* `IsHTop.phiMap_phiMap`: Hermitian tops solve `Φ_μ² y = N² y`, by first variation.
* `IsHTop.proportional_of_bdry_ne_zero`: if every Hermitian top has nonzero boundary functional
  `ℓ_μ(y) = Σ_j μ_j (Hy)_j`, then all Hermitian tops are proportional. Otherwise the combination
  `ℓ(y₂)y₁ − ℓ(y₁)y₂` would be a Hermitian top with `ℓ = 0`.
* `IsTop.isHTop`: every Takagi top is a Hermitian top (Takagi's theorem). From a Hermitian top
  `y` with value `N`, the vector `y + Φy/N` (or `i y`) is a con-eigenvector with `T = N‖·‖²`.
* Along the aperture flow `μ_j = M_j e^{2a p_j}`, the derivative of `R` is rank one and positive:
  `∂_a R = 2|ℓ(y)|²`. A degenerate Hermitian top always contains a vector with `ℓ = 0`, so the top
  value has zero left derivative there.

**Theorem** (`exists_simple_boundary_nondegenerate_window`). Suppose all nodes have the same real
part `δ > 0` and the masses `M_j` are positive. There is a length `L` such that every window
`[a₀, a₀ + L]` of the phase orbit `M_j e^{2a(p_j − δ)}` contains an aperture at which Takagi top
vectors exist, any two of them are proportional (the top is simple), and each has `Σ_k y_k ≠ 0`.

The proof is a chaining argument against the growth `N(a)² ≍ e^{4aδ}` (`chain_contradiction`).
-/

namespace GaloisForLFunctions.HTGeometry.CauchyTakagi

open Matrix Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {m : ℕ}

/-! ## A chaining lemma -/

/-- **Chaining against exponential growth.** A function that cannot drop by more than
`K e^{κa} h²` over a backward step of length `h` cannot grow from `≤ B e^{κa₀}` to
`≥ c₀ e^{κ(a₀+L)}` once `κL ≥ 2 + 2B/c₀`. -/
theorem chain_contradiction {N : ℝ → ℝ} {a₀ L κ c₀ B K h₀ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hh₀ : 0 < h₀) (hL0 : 0 < L) (hL : 2 + 2 * (B / c₀) ≤ κ * L)
    (hlow : c₀ * Real.exp (κ * (a₀ + L)) ≤ N (a₀ + L))
    (hup : N a₀ ≤ B * Real.exp (κ * a₀))
    (hstep : ∀ a h, a₀ ≤ a - h → a ≤ a₀ + L → 0 ≤ h → h ≤ h₀ →
      N a - K * Real.exp (κ * a) * h ^ 2 ≤ N (a - h)) : False := by
  set b : ℝ := a₀ + L with hb_def
  have hEb := Real.exp_pos (κ * b)
  have hchain : ∀ h : ℝ, 0 ≤ h → h ≤ h₀ → ∀ n : ℕ, a₀ + n * h ≤ b →
      N b - n * (K * Real.exp (κ * b) * h ^ 2) ≤ N (b - n * h) := by
    intro h hh hhh n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hb
      push_cast at hb ⊢
      have hb' : a₀ + n * h ≤ b := by nlinarith
      have h1 := ih hb'
      have h2 := hstep (b - n * h) h (by linarith) (by nlinarith) hh hhh
      have hmono : Real.exp (κ * (b - n * h)) ≤ Real.exp (κ * b) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ (n : ℝ) * h := by positivity
        nlinarith
      have hKh : 0 ≤ K * h ^ 2 := by positivity
      rw [show b - (n + 1) * h = b - n * h - h by ring]
      nlinarith [mul_le_mul_of_nonneg_left hmono hKh]
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K * L ^ 2 / c₀ + L / h₀ + 1)
  have hnpos : (0 : ℝ) < n := by
    have : 0 ≤ 2 * K * L ^ 2 / c₀ := by positivity
    have : 0 ≤ L / h₀ := by positivity
    linarith
  set h : ℝ := L / n with hh_def
  have hh : 0 ≤ h := by positivity
  have hnh : (n : ℝ) * h = L := by rw [hh_def]; field_simp
  have hhh : h ≤ h₀ := by
    rw [hh_def, div_le_iff₀ hnpos]
    have : L / h₀ < n := by
      have : 0 ≤ 2 * K * L ^ 2 / c₀ := by positivity
      linarith
    rw [div_lt_iff₀ hh₀] at this
    linarith
  have hc := hchain h hh hhh n (by rw [hnh])
  rw [hnh, show b - L = a₀ by rw [hb_def]; ring] at hc
  have herr : (n : ℝ) * (K * Real.exp (κ * b) * h ^ 2) ≤ c₀ / 2 * Real.exp (κ * b) := by
    have h1 : (n : ℝ) * (K * Real.exp (κ * b) * h ^ 2) = K * L ^ 2 / n * Real.exp (κ * b) := by
      rw [hh_def]; field_simp
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ hEb.le
    rw [div_le_iff₀ hnpos]
    have : 2 * K * L ^ 2 / c₀ < n := by
      have : 0 ≤ L / h₀ := by positivity
      linarith
    rw [div_lt_iff₀ hc₀] at this
    nlinarith
  have hsplit : Real.exp (κ * b) = Real.exp (κ * a₀) * Real.exp (κ * L) := by
    rw [← Real.exp_add, hb_def]; ring_nf
  have hexpL : 3 + 2 * (B / c₀) ≤ Real.exp (κ * L) := by
    have := Real.add_one_le_exp (κ * L)
    linarith
  have hfinal : c₀ / 2 * Real.exp (κ * b) ≤ B * Real.exp (κ * a₀) := by linarith
  rw [hsplit] at hfinal
  have hEa := Real.exp_pos (κ * a₀)
  have hcB : c₀ / 2 * (3 + 2 * (B / c₀)) = 3 * c₀ / 2 + B := by field_simp
  have : c₀ / 2 * Real.exp (κ * L) ≤ B := by
    have h' : Real.exp (κ * a₀) * (c₀ / 2 * Real.exp (κ * L)) ≤ Real.exp (κ * a₀) * B := by
      linarith
    exact le_of_mul_le_mul_left h' hEa
  nlinarith [mul_le_mul_of_nonneg_left hexpL (by positivity : (0 : ℝ) ≤ c₀ / 2)]

/-! ## The `H`-inner product and the con-linear map `Φ` -/

/-- The `H`-inner product `⟨a, b⟩_H = a* H b`. -/
def hInner (p a b : Fin m → ℂ) : ℂ := star a ⬝ᵥ (hGram p *ᵥ b)

/-- The con-linear map `Φ_μ(y) = conj(μ ∘ Hy)`. -/
def phiMap (p μ y : Fin m → ℂ) : Fin m → ℂ := fun j => conj (μ j * (hGram p *ᵥ y) j)

/-- The Hermitian form `R_μ(y) = ‖Φ_μ y‖²_H`. -/
def rForm (p μ y : Fin m → ℂ) : ℝ := gNorm p (phiMap p μ y)

/-- The boundary functional `ℓ_μ(y) = Σ_j μ_j (Hy)_j`. -/
def bdry (p μ y : Fin m → ℂ) : ℂ := ∑ j, μ j * (hGram p *ᵥ y) j

/-- `y` is a Hermitian top vector: it maximizes `R_μ(z)/‖z‖²_H`. -/
def IsHTop (p μ y : Fin m → ℂ) : Prop :=
  y ≠ 0 ∧ ∀ z, rForm p μ z * gNorm p y ≤ rForm p μ y * gNorm p z

theorem gNorm_eq_re_hInner (p y : Fin m → ℂ) : gNorm p y = (hInner p y y).re := rfl

theorem hInner_swap (p a b : Fin m → ℂ) : hInner p a b = conj (hInner p b a) :=
  star_dotProduct_hGram_swap p a b

theorem hInner_self_im (p y : Fin m → ℂ) : (hInner p y y).im = 0 := by
  have h := hInner_swap p y y
  have := congrArg Complex.im h
  rw [conj_im] at this
  linarith

theorem hInner_self_eq (p y : Fin m → ℂ) : hInner p y y = (gNorm p y : ℂ) := by
  apply Complex.ext
  · simp [gNorm_eq_re_hInner]
  · simp [hInner_self_im]

/-- `⟨Φ_μ y, z⟩_H = Σ_j μ_j (Hy)_j (Hz)_j`. -/
theorem hInner_phiMap (p μ y z : Fin m → ℂ) :
    hInner p (phiMap p μ y) z = ∑ j, μ j * (hGram p *ᵥ y) j * (hGram p *ᵥ z) j := by
  simp [hInner, phiMap, dotProduct]

/-- `Φ` is `H`-symmetric: `⟨Φ y, z⟩_H = ⟨Φ z, y⟩_H`. -/
theorem hInner_phiMap_comm (p μ y z : Fin m → ℂ) :
    hInner p (phiMap p μ y) z = hInner p (phiMap p μ z) y := by
  rw [hInner_phiMap, hInner_phiMap]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem tForm_eq_hInner (p μ y : Fin m → ℂ) : tForm p μ y = hInner p (phiMap p μ y) y := by
  rw [hInner_phiMap, tForm]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem hInner_add_left (p a b c : Fin m → ℂ) :
    hInner p (a + b) c = hInner p a c + hInner p b c := by
  simp [hInner, star_add, add_dotProduct]

theorem hInner_add_right (p a b c : Fin m → ℂ) :
    hInner p a (b + c) = hInner p a b + hInner p a c := by
  simp [hInner, mulVec_add, dotProduct_add]

theorem hInner_smul_left (p a b : Fin m → ℂ) (c : ℂ) :
    hInner p (c • a) b = conj c * hInner p a b := by
  simp [hInner, star_smul, smul_dotProduct]

theorem hInner_smul_right (p a b : Fin m → ℂ) (c : ℂ) :
    hInner p a (c • b) = c * hInner p a b := by
  simp [hInner, mulVec_smul, dotProduct_smul]

theorem phiMap_add (p μ y z : Fin m → ℂ) :
    phiMap p μ (y + z) = phiMap p μ y + phiMap p μ z := by
  funext j; simp [phiMap, mulVec_add, mul_add]

theorem phiMap_smul (p μ y : Fin m → ℂ) (c : ℂ) :
    phiMap p μ (c • y) = conj c • phiMap p μ y := by
  funext j; simp [phiMap, mulVec_smul]; ring

theorem phiMap_sub (p μ y z : Fin m → ℂ) :
    phiMap p μ (y - z) = phiMap p μ y - phiMap p μ z := by
  funext j; simp [phiMap, mulVec_sub, mul_sub]

theorem bdry_add (p μ y z : Fin m → ℂ) : bdry p μ (y + z) = bdry p μ y + bdry p μ z := by
  simp [bdry, mulVec_add, mul_add, Finset.sum_add_distrib]

theorem bdry_sub (p μ y z : Fin m → ℂ) : bdry p μ (y - z) = bdry p μ y - bdry p μ z := by
  simp [bdry, mulVec_sub, mul_sub, Finset.sum_sub_distrib]

theorem bdry_smul (p μ y : Fin m → ℂ) (c : ℂ) : bdry p μ (c • y) = c * bdry p μ y := by
  simp [bdry, mulVec_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Cauchy–Schwarz for the `H`-inner product.** -/
theorem normSq_hInner_le {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    (a b : Fin m → ℂ) : ‖hInner p a b‖ ^ 2 ≤ gNorm p a * gNorm p b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [hInner, gNorm]
  have hgb := gNorm_pos hp hinj hb
  set I := hInner p a b with hI
  set c : ℂ := -(conj I / (gNorm p b : ℂ)) with hc
  have hexp : hInner p (a + c • b) (a + c • b) =
      hInner p a a + c * I + conj c * conj I + conj c * c * hInner p b b := by
    rw [hInner_add_left, hInner_add_right, hInner_add_right, hInner_smul_left,
      hInner_smul_left, hInner_smul_right, hInner_smul_right, ← hI, hInner_swap p b a, ← hI]
    ring
  have hnn := gNorm_nonneg hp (a + c • b)
  rw [gNorm_eq_re_hInner, hexp, hInner_self_eq p a, hInner_self_eq p b] at hnn
  have hcI : c * I = -(((‖I‖ ^ 2 / gNorm p b : ℝ)) : ℂ) := by
    rw [hc, neg_mul, div_mul_eq_mul_div, Complex.conj_mul', ofReal_div, ofReal_pow]
  have hcc : conj c * c = (((‖I‖ ^ 2 / gNorm p b ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.conj_mul', hc, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hgb]
    push_cast; ring
  have hcI' : conj c * conj I = conj (c * I) := by rw [map_mul]
  rw [hcI', hcI, hcc] at hnn
  simp only [add_re, ofReal_re, neg_re, conj_re, mul_re, ofReal_im, zero_mul, sub_zero] at hnn
  have key : ‖I‖ ^ 2 / gNorm p b ≤ gNorm p a := by
    have e : ‖I‖ ^ 2 / gNorm p b ^ 2 * gNorm p b = ‖I‖ ^ 2 / gNorm p b := by
      field_simp
    nlinarith
  rw [div_le_iff₀ hgb] at key
  linarith

/-! ## Hermitian tops -/

theorem rForm_smul (p μ z : Fin m → ℂ) (r : ℝ) : rForm p μ ((r : ℂ) • z) = r ^ 2 * rForm p μ z := by
  rw [rForm, phiMap_smul, Complex.conj_ofReal, gNorm_smul, rForm]

theorem continuous_rForm (p μ : Fin m → ℂ) : Continuous (rForm p μ) := by
  unfold rForm gNorm phiMap; simp only [mulVec, dotProduct, Pi.star_apply]; fun_prop

theorem rForm_nonneg {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (μ y : Fin m → ℂ) :
    0 ≤ rForm p μ y := gNorm_nonneg hp _

/-- **Hermitian tops exist.** -/
theorem exists_isHTop {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    (hm : 0 < m) (μ : Fin m → ℂ) : ∃ y, IsHTop p μ y := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hS := isCompact_sphere (0 : Fin m → ℂ) 1
  have hne : (Metric.sphere (0 : Fin m → ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hpos : ∀ u ∈ Metric.sphere (0 : Fin m → ℂ) 1, 0 < gNorm p u := fun u hu =>
    gNorm_pos hp hinj (ne_zero_of_mem_sphere one_ne_zero ⟨u, hu⟩)
  have hcont : ContinuousOn (fun z => rForm p μ z / gNorm p z) (Metric.sphere 0 1) :=
    (continuous_rForm p μ).continuousOn.div (continuous_gNorm p).continuousOn
      fun u hu => (hpos u hu).ne'
  obtain ⟨y, hyS, hymax⟩ := hS.exists_isMaxOn hne hcont
  have hy0 : y ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨y, hyS⟩
  refine ⟨y, hy0, fun z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : rForm p μ 0 = 0 := by
      have := rForm_smul p μ 0 0
      simpa using this
    have h1 : gNorm p 0 = 0 := by simp [gNorm]
    rw [h0, h1]; simp
  obtain ⟨r, hr, u, hu, rfl⟩ := exists_unit_smul hz
  have hmax := hymax hu
  simp only [Set.mem_setOf_eq] at hmax
  rw [div_le_div_iff₀ (hpos u hu) (hpos y hyS)] at hmax
  rw [rForm_smul, gNorm_smul]
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  nlinarith [mul_le_mul_of_nonneg_left hmax hr2]

/-- **Eigen-equation of Hermitian tops.** `Φ² y = N² y` with `N² = R(y)/‖y‖²`. -/
theorem IsHTop.phiMap_phiMap {p μ y : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re)
    (hinj : Function.Injective p) (hy : IsHTop p μ y) :
    phiMap p μ (phiMap p μ y) = ((rForm p μ y / gNorm p y : ℝ) : ℂ) • y := by
  have hg := gNorm_pos hp hinj hy.1
  set N2 : ℝ := rForm p μ y / gNorm p y with hN2
  have hle : ∀ z, rForm p μ z ≤ N2 * gNorm p z := by
    intro z
    have := hy.2 z
    rw [hN2, div_mul_eq_mul_div, le_div_iff₀ hg]
    linarith
  have heq : rForm p μ y = N2 * gNorm p y := by rw [hN2]; field_simp
  -- first variation
  have hvar : ∀ d, (hInner p (phiMap p μ d) (phiMap p μ y)).re =
      N2 * (hInner p d y).re := by
    intro d
    have key : ∀ ε : ℝ, 2 * ε * ((hInner p (phiMap p μ d) (phiMap p μ y)).re -
        N2 * (hInner p d y).re) + ε ^ 2 * (rForm p μ d - N2 * gNorm p d) ≤ 0 := by
      intro ε
      have h := hle (y + (ε : ℂ) • d)
      have h1 : rForm p μ (y + (ε : ℂ) • d) = rForm p μ y +
          2 * ε * (hInner p (phiMap p μ d) (phiMap p μ y)).re + ε ^ 2 * rForm p μ d := by
        rw [rForm, phiMap_add, phiMap_smul, Complex.conj_ofReal, gNorm_add_smul]
        rfl
      have h2 := gNorm_add_smul p y d ε
      rw [h1, h2] at h
      have h3 : (hInner p d y).re = (star d ⬝ᵥ (hGram p *ᵥ y)).re := rfl
      rw [← h3] at h
      nlinarith
    linarith [eq_zero_of_forall_quad_le key]
  set w : Fin m → ℂ := phiMap p μ (phiMap p μ y) - (N2 : ℂ) • y with hw
  have hzero : ∀ d, hInner p w d = 0 := by
    intro d
    have e1 : hInner p (phiMap p μ d) (phiMap p μ y) = hInner p (phiMap p μ (phiMap p μ y)) d :=
      hInner_phiMap_comm p μ d (phiMap p μ y)
    have hre : ∀ d, (hInner p w d).re = 0 := by
      intro d
      have h := hvar d
      rw [hInner_phiMap_comm] at h
      have e2 : hInner p w d = hInner p (phiMap p μ (phiMap p μ y)) d - (N2 : ℂ) * hInner p y d := by
        rw [hw, sub_eq_add_neg, hInner_add_left, ← neg_smul, hInner_smul_left]
        simp [Complex.conj_ofReal]
        ring
      rw [e2, sub_re, re_ofReal_mul]
      have e3 : (hInner p y d).re = (hInner p d y).re := by
        rw [hInner_swap p y d, conj_re]
      rw [e3]; linarith
    apply Complex.ext
    · exact hre d
    · have h := hre (I • d)
      rw [hInner_smul_right, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub] at h
      simpa using h
  have hw0 : w = 0 := by
    by_contra hne
    have := gNorm_pos hp hinj hne
    rw [gNorm_eq_re_hInner, hzero w, zero_re] at this
    exact lt_irrefl 0 this
  rw [hw, sub_eq_zero] at hw0
  exact hw0

/-- The value of a Hermitian top: `R(y) = N² ‖y‖²` for every solution of `Φ² y = N² y`. -/
theorem rForm_of_phiMap_phiMap {p μ z : Fin m → ℂ} {N2 : ℝ}
    (hz : phiMap p μ (phiMap p μ z) = (N2 : ℂ) • z) : rForm p μ z = N2 * gNorm p z := by
  have e : hInner p (phiMap p μ z) (phiMap p μ z) = (N2 : ℂ) * hInner p z z := by
    rw [hInner_phiMap_comm, hz, hInner_smul_left, Complex.conj_ofReal]
  rw [rForm, gNorm_eq_re_hInner, e, re_ofReal_mul, ← gNorm_eq_re_hInner]

/-- **Simplicity.** If every Hermitian top has nonzero boundary functional, any two Hermitian tops
are proportional. -/
theorem IsHTop.proportional_of_bdry_ne_zero {p μ y₁ y₂ : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re)
    (hinj : Function.Injective p) (h₁ : IsHTop p μ y₁) (h₂ : IsHTop p μ y₂)
    (hall : ∀ y, IsHTop p μ y → bdry p μ y ≠ 0) :
    y₂ = (bdry p μ y₂ / bdry p μ y₁) • y₁ := by
  have hg₁ := gNorm_pos hp hinj h₁.1
  have hg₂ := gNorm_pos hp hinj h₂.1
  set N2 : ℝ := rForm p μ y₁ / gNorm p y₁ with hN2
  have hN2' : rForm p μ y₂ / gNorm p y₂ = N2 := by
    have a1 := h₁.2 y₂
    have a2 := h₂.2 y₁
    rw [hN2, div_eq_div_iff hg₂.ne' hg₁.ne']
    linarith
  have e₁ := h₁.phiMap_phiMap hp hinj
  have e₂ := h₂.phiMap_phiMap hp hinj
  rw [← hN2] at e₁
  rw [hN2'] at e₂
  set z : Fin m → ℂ := bdry p μ y₂ • y₁ - bdry p μ y₁ • y₂ with hz
  have hphi2 : ∀ (c : ℂ) (y : Fin m → ℂ), phiMap p μ (phiMap p μ (c • y)) =
      c • phiMap p μ (phiMap p μ y) := by
    intro c y
    rw [phiMap_smul, phiMap_smul, Complex.conj_conj]
  have hz2 : phiMap p μ (phiMap p μ z) = (N2 : ℂ) • z := by
    rw [hz, phiMap_sub, phiMap_sub, hphi2, hphi2, e₁, e₂, smul_sub, smul_comm (N2 : ℂ),
      smul_comm (N2 : ℂ) (bdry p μ y₁)]
  have hbz : bdry p μ z = 0 := by
    rw [hz, bdry_sub, bdry_smul, bdry_smul]
    ring
  have hz0 : z = 0 := by
    by_contra hne
    apply hall z ⟨hne, fun w => ?_⟩ hbz
    have hR := rForm_of_phiMap_phiMap hz2
    have hw := h₁.2 w
    rw [hR]
    have : rForm p μ w ≤ N2 * gNorm p w := by
      rw [hN2, div_mul_eq_mul_div, le_div_iff₀ hg₁]; linarith
    have hgz := gNorm_nonneg hp z
    nlinarith
  have hb₁ := hall y₁ h₁
  rw [hz, sub_eq_zero] at hz0
  funext j
  have := congrFun hz0 j
  simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
  field_simp
  linear_combination -this

/-- **Takagi's theorem in the `H`-geometry.** Every Takagi top is a Hermitian top. -/
theorem IsTop.isHTop {p μ y : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    (hm : 0 < m) (hy : IsTop p μ y) : IsHTop p μ y := by
  obtain ⟨yH, hyH⟩ := exists_isHTop hp hinj hm μ
  have hgH := gNorm_pos hp hinj hyH.1
  have hgT := gNorm_pos hp hinj hy.1
  set N2 : ℝ := rForm p μ yH / gNorm p yH with hN2
  have hN2nn : 0 ≤ N2 := div_nonneg (rForm_nonneg hp μ yH) hgH.le
  have hRle : ∀ z, rForm p μ z ≤ N2 * gNorm p z := by
    intro z
    have := hyH.2 z
    rw [hN2, div_mul_eq_mul_div, le_div_iff₀ hgH]; linarith
  have hCS : ∀ z, ‖tForm p μ z‖ ^ 2 ≤ rForm p μ z * gNorm p z := by
    intro z
    rw [tForm_eq_hInner]
    exact normSq_hInner_le hp hinj _ _
  -- a con-eigenvector with value `√N2`
  set N : ℝ := Real.sqrt N2 with hN
  have hNsq : N ^ 2 = N2 := Real.sq_sqrt hN2nn
  have heig := hyH.phiMap_phiMap hp hinj
  rw [← hN2] at heig
  have hTge : ∃ z, z ≠ 0 ∧ N * gNorm p z ≤ ‖tForm p μ z‖ := by
    rcases eq_or_lt_of_le (Real.sqrt_nonneg N2) with h0 | hNpos
    · have hN0 : N = 0 := by rw [hN, ← h0]
      exact ⟨yH, hyH.1, by rw [hN0, zero_mul]; exact norm_nonneg _⟩
    · rw [← hN] at hNpos
      set z : Fin m → ℂ := yH + ((N⁻¹ : ℝ) : ℂ) • phiMap p μ yH with hz
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
      have hphiz : phiMap p μ z = (N : ℂ) • z := by
        rw [hz, phiMap_add, phiMap_smul, Complex.conj_ofReal, heig, smul_add, smul_smul,
          smul_smul]
        have h1 : ((N⁻¹ : ℝ) : ℂ) * (N2 : ℂ) = (N : ℂ) := by
          rw [← hNsq]; push_cast; field_simp
        have h2 : (N : ℂ) * ((N⁻¹ : ℝ) : ℂ) = 1 := by
          push_cast; field_simp
        rw [h1, h2, one_smul, add_comm]
      rcases eq_or_ne z 0 with hz0 | hz0
      · -- then `Φ yH = −N yH`; use `i yH`
        have hphiy : phiMap p μ yH = -((N : ℂ) • yH) := by
          have := hz0
          rw [hz] at this
          have h' : ((N⁻¹ : ℝ) : ℂ) • phiMap p μ yH = -yH := eq_neg_of_add_eq_zero_right this
          have h'' := congrArg (fun v => ((N : ℝ) : ℂ) • v) h'
          simp only [smul_smul, ← ofReal_mul, mul_inv_cancel₀ hNpos.ne', ofReal_one,
            one_smul, smul_neg] at h''
          exact h''
        refine ⟨I • yH, by simpa using hyH.1, ?_⟩
        have hphiI : phiMap p μ (I • yH) = (N : ℂ) • (I • yH) := by
          rw [phiMap_smul, conj_I, hphiy, smul_neg, neg_smul, neg_neg, smul_comm]
        rw [tForm_eq_hInner, hphiI, hInner_smul_left, Complex.conj_ofReal, hInner_self_eq,
          norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hNpos, abs_of_nonneg (gNorm_nonneg hp _)]
      · refine ⟨z, hz0, ?_⟩
        rw [tForm_eq_hInner, hphiz, hInner_smul_left, Complex.conj_ofReal, hInner_self_eq,
          norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hNpos, abs_of_nonneg (gNorm_nonneg hp _)]
  obtain ⟨z, hz0, hTz⟩ := hTge
  have hgz := gNorm_pos hp hinj hz0
  -- `|T(y)| ≥ N ‖y‖²` at the Takagi top
  have hTy : N * gNorm p y ≤ ‖tForm p μ y‖ := by
    have := hy.2 z
    have h1 : N * gNorm p z * gNorm p y ≤ ‖tForm p μ z‖ * gNorm p y :=
      mul_le_mul_of_nonneg_right hTz hgT.le
    have h2 : N * gNorm p y * gNorm p z ≤ ‖tForm p μ y‖ * gNorm p z := by nlinarith
    exact le_of_mul_le_mul_right h2 hgz
  have hRy : N2 * gNorm p y ≤ rForm p μ y := by
    have h1 := hCS y
    have h2 : (N * gNorm p y) ^ 2 ≤ ‖tForm p μ y‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hgT.le) hTy 2
    rw [mul_pow, hNsq] at h2
    have h3 : N2 * gNorm p y ^ 2 ≤ rForm p μ y * gNorm p y := by linarith
    have h4 : N2 * gNorm p y * gNorm p y ≤ rForm p μ y * gNorm p y := by nlinarith
    exact le_of_mul_le_mul_right h4 hgT
  refine ⟨hy.1, fun w => ?_⟩
  have := hRle w
  have hgw := gNorm_nonneg hp w
  nlinarith [mul_le_mul_of_nonneg_right hRy hgw, mul_le_mul_of_nonneg_right this hgT.le]


/-! ## The Hermitian top along the aperture flow -/

theorem rForm_eq_sum (p μ y : Fin m → ℂ) :
    rForm p μ y = (∑ j, ∑ k, μ j * (hGram p *ᵥ y) j * conj (μ k * (hGram p *ᵥ y) k) *
      hGram p j k).re := by
  rw [rForm, gNorm]
  congr 1
  simp only [dotProduct, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (hGram p *ᵥ phiMap p μ y) j = ∑ k, hGram p j k * phiMap p μ y k from rfl,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [phiMap, Complex.conj_conj]
  ring

theorem norm_hGram_le {δ : ℝ} (hδ : 0 < δ) {p : Fin m → ℂ} (hre : ∀ j, (p j).re = δ)
    (j k : Fin m) : ‖hGram p j k‖ ≤ 1 / (2 * δ) := by
  rw [hGram_apply, norm_inv, one_div]
  have hq : 2 * δ ≤ ‖p j + conj (p k)‖ := by
    have := Complex.abs_re_le_norm (p j + conj (p k))
    rw [add_re, conj_re, hre j, hre k, abs_of_pos (by linarith)] at this
    linarith
  exact inv_anti₀ (by positivity) hq

theorem re_sum_sesq_le {C : ℝ} {G : Fin m → Fin m → ℂ} (hG : ∀ j k, ‖G j k‖ ≤ C)
    (x : Fin m → ℂ) : (∑ j, ∑ k, x j * conj (x k) * G j k).re ≤ C * (∑ j, ‖x j‖) ^ 2 := by
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  rw [show C * (∑ j, ‖x j‖) ^ 2 = ∑ j, ∑ k, C * (‖x j‖ * ‖x k‖) by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]]
  refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have := hG j k
  have h0 : 0 ≤ ‖x j‖ * ‖x k‖ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this h0]

theorem rForm_of_unit {δ : ℝ} {p : Fin m → ℂ} (hre : ∀ j, (p j).re = δ) (μ y : Fin m → ℂ)
    (j₀ : Fin m) (hy : hGram p *ᵥ y = Pi.single j₀ 1) :
    rForm p μ y = ‖μ j₀‖ ^ 2 / (2 * δ) := by
  rw [rForm_eq_sum, hy, Finset.sum_eq_single j₀ (fun j _ hj => by simp [Pi.single_apply, hj])
    (by simp), Finset.sum_eq_single j₀ (fun k _ hk => by simp [hk]) (by simp)]
  have hH : hGram p j₀ j₀ = (((2 * δ)⁻¹ : ℝ) : ℂ) := by
    rw [hGram_apply, Complex.add_conj, hre j₀]; push_cast; ring
  simp only [Pi.single_eq_same, mul_one]
  rw [Complex.mul_conj', hH, ← ofReal_pow, ← ofReal_mul, ofReal_re]
  ring

/-- **The rank-one flow step.** At a vector with `ℓ(y) = 0`, a backward step of the aperture flow
lowers `R` by at most `8h²P(Σ_j |μ_j (Hy)_j|)²`. -/
theorem rForm_flow_step {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (M : Fin m → ℝ) {P : ℝ}
    (hP : ∀ j, ‖p j‖ ≤ P) {a h : ℝ} (hh : 0 ≤ h) (hhP : 4 * h * P ≤ 1) (y : Fin m → ℂ)
    (hb : bdry p (flowMass p M a) y = 0) :
    rForm p (flowMass p M a) y -
        8 * h ^ 2 * P * (∑ j, ‖flowMass p M a j * (hGram p *ᵥ y) j‖) ^ 2 ≤
      rForm p (flowMass p M (a - h)) y := by
  set v := hGram p *ᵥ y with hv
  set x : Fin m → ℂ := fun j => flowMass p M a j * v j with hx
  set q : Fin m → Fin m → ℂ := fun j k => p j + conj (p k) with hq
  set E : Fin m → Fin m → ℂ := fun j k =>
    Complex.exp (-(2 * h * q j k)) - 1 - (-(2 * h * q j k)) with hE
  have hterm : ∀ j k, flowMass p M (a - h) j * v j * conj (flowMass p M (a - h) k * v k) *
      hGram p j k = x j * conj (x k) * hGram p j k - 2 * h * (x j * conj (x k)) +
        x j * conj (x k) * E j k * hGram p j k := by
    intro j k
    have hc : conj (Complex.exp (-(2 * h * p k))) = Complex.exp (-(2 * h * conj (p k))) := by
      rw [← Complex.exp_conj, map_neg, map_mul, map_mul, Complex.conj_ofReal, map_ofNat]
    have hexp : Complex.exp (-(2 * h * p j)) * Complex.exp (-(2 * h * conj (p k))) =
        Complex.exp (-(2 * h * q j k)) := by
      rw [← Complex.exp_add]; congr 1; simp only [hq]; ring
    have hHq : hGram p j k * q j k = 1 := by
      rw [hGram_apply]; exact inv_mul_cancel₀ (add_conj_ne_zero hp j k)
    rw [flowMass_sub, flowMass_sub]
    simp only [hx, hE, map_mul, hc]
    linear_combination (flowMass p M a j * v j * (conj (flowMass p M a k) * conj (v k)) *
      hGram p j k) * hexp + (-(2 * (h : ℂ)) * (flowMass p M a j * v j *
        (conj (flowMass p M a k) * conj (v k)))) * hHq
  have hsumX : ∑ j, ∑ k, x j * conj (x k) = 0 := by
    have : ∑ j, ∑ k, x j * conj (x k) = bdry p (flowMass p M a) y * conj (bdry p (flowMass p M a) y) := by
      rw [bdry, map_sum, Finset.sum_mul_sum]
    rw [this, hb, zero_mul]
  have hsplit : rForm p (flowMass p M (a - h)) y = rForm p (flowMass p M a) y +
      (∑ j, ∑ k, x j * conj (x k) * E j k * hGram p j k).re := by
    rw [rForm_eq_sum, rForm_eq_sum]
    have h1 : ∑ j, ∑ k, flowMass p M (a - h) j * v j * conj (flowMass p M (a - h) k * v k) *
        hGram p j k = ∑ j, ∑ k, x j * conj (x k) * hGram p j k -
          2 * h * (∑ j, ∑ k, x j * conj (x k)) +
            ∑ j, ∑ k, x j * conj (x k) * E j k * hGram p j k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => hterm j k
    rw [h1, hsumX, mul_zero, sub_zero, add_re]
  have hEH : ∀ j k, ‖E j k * hGram p j k‖ ≤ 8 * h ^ 2 * P := by
    intro j k
    have hqn : ‖q j k‖ ≤ 2 * P := by
      simp only [hq]
      calc ‖p j + conj (p k)‖ ≤ ‖p j‖ + ‖conj (p k)‖ := norm_add_le _ _
        _ = ‖p j‖ + ‖p k‖ := by rw [Complex.norm_conj]
        _ ≤ 2 * P := by linarith [hP j, hP k]
    have hq0 : 0 < ‖q j k‖ := norm_pos_iff.mpr (add_conj_ne_zero hp j k)
    have hn : ‖-(2 * h * q j k)‖ = 2 * h * ‖q j k‖ := by
      rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh,
        Complex.norm_ofNat]
    have hle1 : ‖-(2 * h * q j k)‖ ≤ 1 := by rw [hn]; nlinarith
    have hEn : ‖E j k‖ ≤ (2 * h * ‖q j k‖) ^ 2 := by
      have := Complex.norm_exp_sub_one_sub_id_le hle1
      rw [hn] at this; exact this
    rw [norm_mul, hGram_apply, norm_inv]
    calc ‖E j k‖ * ‖q j k‖⁻¹ ≤ (2 * h * ‖q j k‖) ^ 2 * ‖q j k‖⁻¹ :=
          mul_le_mul_of_nonneg_right hEn (inv_nonneg.mpr hq0.le)
      _ = 4 * h ^ 2 * ‖q j k‖ := by field_simp; ring
      _ ≤ 4 * h ^ 2 * (2 * P) := by gcongr
      _ = 8 * h ^ 2 * P := by ring
  have herr : |(∑ j, ∑ k, x j * conj (x k) * E j k * hGram p j k).re| ≤
      8 * h ^ 2 * P * (∑ j, ‖x j‖) ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans ?_
    rw [show (∑ j, ‖x j‖) ^ 2 = ∑ j, ∑ k, ‖x j‖ * ‖x k‖ by rw [sq, Finset.sum_mul_sum],
      Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [show x j * conj (x k) * E j k * hGram p j k = x j * conj (x k) * (E j k * hGram p j k) by
      ring, norm_mul, norm_mul, Complex.norm_conj]
    have := hEH j k
    have h0 : 0 ≤ ‖x j‖ * ‖x k‖ := by positivity
    nlinarith
  rw [hsplit]
  have := (abs_le.mp herr).1
  simp only [hx] at this
  linarith

/-- **Simple and boundary-nondegenerate tops in every window.** -/
theorem exists_simple_boundary_nondegenerate_window {δ : ℝ} (hδ : 0 < δ) {p : Fin m → ℂ}
    (hre : ∀ j, (p j).re = δ) (hinj : Function.Injective p) {M : Fin m → ℝ}
    (hM : ∀ j, 0 < M j) (hm : 0 < m) :
    ∃ L : ℝ, 0 < L ∧ ∀ a₀ : ℝ, ∃ a, a₀ ≤ a ∧ a ≤ a₀ + L ∧
      (∃ y, IsTop p (phaseMass δ p M a) y) ∧
      (∀ y₁ y₂, IsTop p (phaseMass δ p M a) y₁ → IsTop p (phaseMass δ p M a) y₂ →
        ∃ c : ℂ, y₂ = c • y₁) ∧
      ∀ y, IsTop p (phaseMass δ p M a) y → ∑ j, y j ≠ 0 := by
  have hp : ∀ j, 0 < (p j).re := fun j => (hre j).symm ▸ hδ
  have hM0 : ∀ j, 0 ≤ M j := fun j => (hM j).le
  have hiff : ∀ a y, IsTop p (flowMass p M a) y ↔ IsTop p (phaseMass δ p M a) y := fun a y => by
    rw [flowMass_eq δ]; exact isTop_mass_smul_iff _ _ _ (Real.exp_pos _)
  obtain ⟨B, hB0, hB⟩ := exists_mass_bound hp hinj M
  set P : ℝ := ∑ j, ‖p j‖ with hP_def
  have hP : ∀ j, ‖p j‖ ≤ P := fun j =>
    Finset.single_le_sum (fun i _ => norm_nonneg (p i)) (Finset.mem_univ j)
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => norm_nonneg _
  set SM : ℝ := ∑ j, M j with hSM
  have hSM0 : 0 ≤ SM := Finset.sum_nonneg fun j _ => hM0 j
  have hMle : ∀ j, M j ≤ SM := fun j => Finset.single_le_sum (fun i _ => hM0 i) (Finset.mem_univ j)
  set j₀ : Fin m := ⟨0, hm⟩
  obtain ⟨y₁, hy₁, hHy₁⟩ := exists_unit_value hp hinj j₀
  have hg₁ := gNorm_pos hp hinj hy₁
  set c₀ : ℝ := M j₀ ^ 2 / (2 * δ) / gNorm p y₁ with hc₀_def
  have hc₀ : 0 < c₀ := by have := hM j₀; positivity
  set B' : ℝ := (m : ℝ) * SM * B / (2 * δ) with hB'_def
  have hB'0 : 0 ≤ B' := by positivity
  set K : ℝ := 8 * P * ((m : ℝ) * SM * B) with hK_def
  have hK0 : 0 ≤ K := by positivity
  set h₀ : ℝ := 1 / (4 * P + 1) with hh₀_def
  have hh₀ : 0 < h₀ := by positivity
  have hh₀P : ∀ h, 0 ≤ h → h ≤ h₀ → 4 * h * P ≤ 1 := by
    intro h hh hhh
    have : h * (4 * P + 1) ≤ 1 := by
      rw [hh₀_def, le_div_iff₀ (by positivity)] at hhh; linarith
    nlinarith
  set L : ℝ := (2 + 2 * (B' / c₀)) / (4 * δ) with hL_def
  have hL : 0 < L := by have : 0 ≤ B' / c₀ := by positivity
                        positivity
  have hκL : 2 + 2 * (B' / c₀) ≤ 4 * δ * L := by rw [hL_def]; field_simp; rfl
  -- sum of weighted values
  have hxsum : ∀ (a : ℝ) (y : Fin m → ℂ),
      (∑ j, ‖flowMass p M a j * (hGram p *ᵥ y) j‖) ^ 2 ≤
        Real.exp (4 * a * δ) * ((m : ℝ) * SM * B) * gNorm p y := by
    intro a y
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => ‖flowMass p M a j * (hGram p *ᵥ y) j‖)
    have h2 : ∀ j, ‖flowMass p M a j * (hGram p *ᵥ y) j‖ ^ 2 ≤
        Real.exp (4 * a * δ) * SM * (M j * ‖(hGram p *ᵥ y) j‖ ^ 2) := by
      intro j
      rw [norm_mul, norm_flowMass hre hM0, mul_pow, mul_pow,
        show Real.exp (2 * a * δ) ^ 2 = Real.exp (4 * a * δ) by
          rw [← Real.exp_nat_mul]; ring_nf]
      have := hMle j
      have h0 : 0 ≤ M j * ‖(hGram p *ᵥ y) j‖ ^ 2 := mul_nonneg (hM0 j) (by positivity)
      have hE := Real.exp_pos (4 * a * δ)
      nlinarith [mul_le_mul_of_nonneg_right this h0]
    have h3 : ∑ j, ‖flowMass p M a j * (hGram p *ᵥ y) j‖ ^ 2 ≤
        Real.exp (4 * a * δ) * SM * (B * gNorm p y) := by
      refine (Finset.sum_le_sum fun j _ => h2 j).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hB y) (by positivity)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_le_mul_of_nonneg_left h3 hm0]
  refine ⟨L, hL, fun a₀ => ?_⟩
  -- the Hermitian window statement
  have hherm : ∃ a, a₀ ≤ a ∧ a ≤ a₀ + L ∧
      ∀ y, IsHTop p (flowMass p M a) y → bdry p (flowMass p M a) y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hdeg : ∀ a : ℝ, ∃ y, a₀ ≤ a → a ≤ a₀ + L →
        IsHTop p (flowMass p M a) y ∧ bdry p (flowMass p M a) y = 0 := by
      intro a
      by_cases ha : a₀ ≤ a ∧ a ≤ a₀ + L
      · obtain ⟨y, hy, hs⟩ := hcon a ha.1 ha.2
        exact ⟨y, fun _ _ => ⟨hy, hs⟩⟩
      · exact ⟨0, fun h h' => absurd ⟨h, h'⟩ ha⟩
    choose Y hY using hdeg
    set N : ℝ → ℝ := fun a => rForm p (flowMass p M a) (Y a) / gNorm p (Y a) with hN_def
    have hF1 : ∀ a, a₀ ≤ a → a ≤ a₀ + L → ∀ z, rForm p (flowMass p M a) z ≤ N a * gNorm p z := by
      intro a ha ha' z
      have hy := (hY a ha ha').1
      have hg := gNorm_pos hp hinj hy.1
      rw [hN_def, div_mul_eq_mul_div, le_div_iff₀ hg]
      exact hy.2 z
    have hlow : c₀ * Real.exp (4 * δ * (a₀ + L)) ≤ N (a₀ + L) := by
      have h1 := hF1 (a₀ + L) (by linarith) le_rfl y₁
      have hR1 : rForm p (flowMass p M (a₀ + L)) y₁ =
          M j₀ ^ 2 * Real.exp (4 * (a₀ + L) * δ) / (2 * δ) := by
        rw [rForm_of_unit hre _ y₁ j₀ hHy₁, norm_flowMass hre hM0, mul_pow,
          show Real.exp (2 * (a₀ + L) * δ) ^ 2 = Real.exp (4 * (a₀ + L) * δ) by
            rw [← Real.exp_nat_mul]; ring_nf]
      rw [hR1] at h1
      rw [hc₀_def, show 4 * δ * (a₀ + L) = 4 * (a₀ + L) * δ by ring]
      rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : M j₀ ^ 2 * Real.exp (4 * (a₀ + L) * δ) ≤ N (a₀ + L) * gNorm p y₁ * (2 * δ) := by
        rw [div_le_iff₀ (by positivity)] at h1; linarith
      linarith
    have hup : N a₀ ≤ B' * Real.exp (4 * δ * a₀) := by
      have hy := (hY a₀ le_rfl (by linarith)).1
      have hg := gNorm_pos hp hinj hy.1
      have hR : rForm p (flowMass p M a₀) (Y a₀) ≤
          Real.exp (4 * a₀ * δ) * ((m : ℝ) * SM * B) * gNorm p (Y a₀) / (2 * δ) := by
        rw [rForm_eq_sum]
        have h1 := re_sum_sesq_le (norm_hGram_le hδ hre)
          (fun j => flowMass p M a₀ j * (hGram p *ᵥ Y a₀) j)
        have hb := hxsum a₀ (Y a₀)
        refine h1.trans ?_
        rw [one_div, inv_mul_eq_div]
        exact (div_le_div_iff_of_pos_right (by positivity)).mpr hb
      rw [hN_def, div_le_iff₀ hg, hB'_def, show 4 * δ * a₀ = 4 * a₀ * δ by ring]
      calc rForm p (flowMass p M a₀) (Y a₀)
          ≤ Real.exp (4 * a₀ * δ) * ((m : ℝ) * SM * B) * gNorm p (Y a₀) / (2 * δ) := hR
        _ = (m : ℝ) * SM * B / (2 * δ) * Real.exp (4 * a₀ * δ) * gNorm p (Y a₀) := by ring
    refine chain_contradiction (N := N) (κ := 4 * δ) (by positivity) hc₀ hB'0 hK0 hh₀ hL hκL
      hlow hup fun a h hah ha' hh hhh => ?_
    have ha : a₀ ≤ a := by linarith
    have hy := hY a ha ha'
    have hg := gNorm_pos hp hinj hy.1.1
    have hstep := rForm_flow_step hp M hP hh (hh₀P h hh hhh) (Y a) hy.2
    have hmax := hF1 (a - h) hah (by linarith) (Y a)
    have hx := hxsum a (Y a)
    have hNa : rForm p (flowMass p M a) (Y a) = N a * gNorm p (Y a) := by
      rw [hN_def]; field_simp
    have h8 : 0 ≤ 8 * h ^ 2 * P := by positivity
    have hstep' : N a * gNorm p (Y a) - K * Real.exp (4 * δ * a) * h ^ 2 * gNorm p (Y a) ≤
        N (a - h) * gNorm p (Y a) := by
      have e : K * Real.exp (4 * δ * a) * h ^ 2 * gNorm p (Y a) =
          8 * h ^ 2 * P * (Real.exp (4 * a * δ) * ((m : ℝ) * SM * B) * gNorm p (Y a)) := by
        rw [hK_def, show 4 * δ * a = 4 * a * δ by ring]; ring
      rw [e, ← hNa]
      nlinarith [mul_le_mul_of_nonneg_left hx h8]
    have := le_of_mul_le_mul_right (by linarith : (N a - K * Real.exp (4 * δ * a) * h ^ 2) *
      gNorm p (Y a) ≤ N (a - h) * gNorm p (Y a)) hg
    exact this
  obtain ⟨a, ha, ha', hall⟩ := hherm
  refine ⟨a, ha, ha', ?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := exists_isTop hp hinj hm (phaseMass δ p M a)
    exact ⟨y, hy⟩
  · intro y₁ y₂ h₁ h₂
    have H₁ := ((hiff a y₁).mpr h₁).isHTop hp hinj hm
    have H₂ := ((hiff a y₂).mpr h₂).isHTop hp hinj hm
    exact ⟨_, IsHTop.proportional_of_bdry_ne_zero hp hinj H₁ H₂ hall⟩
  · intro y hy hsum
    have hT := (hiff a y).mpr hy
    have hTne : tForm p (flowMass p M a) y ≠ 0 := by
      intro h0
      have h1 := hT.2 y₁
      have hT1 : tForm p (flowMass p M a) y₁ = flowMass p M a j₀ := by
        simp [tForm, hHy₁, Pi.single_apply]
      rw [h0, hT1, norm_zero, zero_mul, norm_flowMass hre hM0] at h1
      have hg := gNorm_pos hp hinj hT.1
      have : 0 < M j₀ * Real.exp (2 * a * δ) * gNorm p y := by
        have := hM j₀; positivity
      linarith
    have hvar := hT.variational hp hinj hTne
    have hL := fun j => lagrange hp hinj hvar.1 hvar.2 j
    have hsumL : conj (tForm p (flowMass p M a) y) / (‖tForm p (flowMass p M a) y‖ : ℂ) *
        bdry p (flowMass p M a) y = 0 := by
      rw [bdry, Finset.mul_sum, Finset.sum_congr rfl fun j _ => hL j, ← Finset.mul_sum,
        ← map_sum, hsum, map_zero, mul_zero]
    have hc : conj (tForm p (flowMass p M a) y) / (‖tForm p (flowMass p M a) y‖ : ℂ) ≠ 0 := by
      apply div_ne_zero
      · exact (map_ne_zero _).mpr hTne
      · exact_mod_cast (norm_pos_iff.mpr hTne).ne'
    have hbd := hall y ((hT).isHTop hp hinj hm)
    exact hbd ((mul_eq_zero.mp hsumL).resolve_left hc)

end

end GaloisForLFunctions.HTGeometry.CauchyTakagi
