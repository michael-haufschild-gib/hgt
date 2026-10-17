import GaloisForLFunctions.HTGeometry.AnalyticMarkovSystem
import GaloisForLFunctions.HTGeometry.WeightedCompositionTrace
import GaloisForLFunctions.HTGeometry.GeometricDecayFredholmDeterminant

/-!
# The transfer matrix of an analytic Markov system

For an analytic Markov system `S` and `s ∈ ℂ`, the transfer operator
`(L_s f)_a = Σ_{src e = a} (φ_e′)^s · f_{tgt e} ∘ φ_e` acts on families of holomorphic functions on the
Markov discs.  In the bases `((z − c_a)/ρ_a)^i`, `ρ_a = ϑ R_a`, `ϑ = √((1 + θ)/2)`, its matrix is
`entry s (a, i) (b, j) = Σ_{src e = a, tgt e = b} coeff_{a,i}(e^{s ℓ_e} ((φ_e − c_b)/ρ_b)^j)`, and `mat s`
is this matrix on `ℕ` through `(a, i) ↦ p i + a` (`decode`).

* `differentiable_coeff_exp_mul`: coefficients of `e^{sℓ} g` are entire in `s`.
* `geomDecay_mat`: `|mat s m n| ≤ C η^m η^n` with `η^p = ϑ < 1`, uniformly for `|s| ≤ r`.
* `ipow_mat_decode`: the entries of `(mat s)^{m+1}` are sums over admissible words of length `m + 1`
  of the coefficients of the composite weighted branches (substitution lemma `hasSum_coeff_comp`).
* `itrace_mat` (**trace formula**): `Tr (mat s)^{m+1} = Σ_{closed words P} e^{sΛ_P}/(1 − e^{Λ_P})`, from
  the residue formula `hasSum_coeff_diag` at the periodic point of each closed word.
-/

open Complex Metric Set Filter Topology MeasureTheory Finset
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace DiscCoefficients

/-- **The coefficients of `e^{sℓ} g` are entire in `s`.** -/
theorem differentiable_coeff_exp_mul {c : ℂ} {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ) {ℓ g : ℂ → ℂ}
    (hℓ : ContinuousOn ℓ (sphere c R)) (hg : ContinuousOn g (sphere c R)) (i : ℕ) :
    Differentiable ℂ fun s : ℂ => coeff c R ρ i (fun z => Complex.exp (s * ℓ z) * g z) := by
  obtain ⟨L, hL⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hℓ
  obtain ⟨G, hG⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hg
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL (c + R) (by simp [abs_of_pos hR]))
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG (c + R) (by simp [abs_of_pos hR]))
  -- the power series in `s`
  set A : ℕ → ℂ := fun k => coeff c R ρ i (fun z => ℓ z ^ k * g z) with hA
  have hAb : ∀ k, ‖A k‖ ≤ L ^ k * G * (ρ / R) ^ i := fun k =>
    norm_coeff_le hR hρ (fun z hz => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hL z hz) k) (hG z hz) (norm_nonneg _)
        (by positivity)) i
  have hrep : ∀ s : ℂ, HasSum (fun k => s ^ k / (k.factorial : ℂ) * A k)
      (coeff c R ρ i (fun z => Complex.exp (s * ℓ z) * g z)) := by
    intro s
    have hcont : ∀ k, ContinuousOn (fun z => ((z - c) ^ (i + 1))⁻¹ *
        (s ^ k / (k.factorial : ℂ) * (ℓ z ^ k * g z))) (sphere c R) := by
      intro k
      refine ContinuousOn.mul ?_ (continuousOn_const.mul ((hℓ.pow k).mul hg))
      refine (ContinuousOn.pow (continuousOn_id.sub continuousOn_const) _).inv₀ fun z hz => ?_
      have := norm_sub_eq_of_mem_sphere hz
      exact pow_ne_zero _ (show z - c ≠ 0 from fun h => by rw [h, norm_zero] at this; linarith)
    have hbd : ∀ k, ∀ z ∈ sphere c R, ‖((z - c) ^ (i + 1))⁻¹ *
        (s ^ k / (k.factorial : ℂ) * (ℓ z ^ k * g z))‖ ≤
          (R ^ (i + 1))⁻¹ * G * ((‖s‖ * L) ^ k / k.factorial) := by
      intro k z hz
      rw [norm_mul, norm_inv, norm_pow, norm_sub_eq_of_mem_sphere hz, norm_mul, norm_div, norm_pow,
        Complex.norm_natCast, norm_mul, norm_pow]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hL z hz) k
      have h2 := hG z hz
      calc (R ^ (i + 1))⁻¹ * (‖s‖ ^ k / k.factorial * (‖ℓ z‖ ^ k * ‖g z‖))
          ≤ (R ^ (i + 1))⁻¹ * (‖s‖ ^ k / k.factorial * (L ^ k * G)) := by gcongr
        _ = (R ^ (i + 1))⁻¹ * G * ((‖s‖ * L) ^ k / k.factorial) := by rw [mul_pow]; ring
    have hsum : Summable fun k => (R ^ (i + 1))⁻¹ * G * ((‖s‖ * L) ^ k / k.factorial) :=
      (Real.summable_pow_div_factorial _).mul_left _
    have hpt : ∀ z ∈ sphere c R, HasSum (fun k => ((z - c) ^ (i + 1))⁻¹ *
        (s ^ k / (k.factorial : ℂ) * (ℓ z ^ k * g z)))
          (((z - c) ^ (i + 1))⁻¹ * (Complex.exp (s * ℓ z) * g z)) := by
      intro z _
      have h := NormedSpace.expSeries_div_hasSum_exp (s * ℓ z)
      rw [← Complex.exp_eq_exp_ℂ] at h
      have h2 := (h.mul_right (g z)).mul_left (((z - c) ^ (i + 1))⁻¹)
      have e : (fun k => ((z - c) ^ (i + 1))⁻¹ * (s ^ k / (k.factorial : ℂ) * (ℓ z ^ k * g z))) =
          fun k => ((z - c) ^ (i + 1))⁻¹ * ((s * ℓ z) ^ k / (k.factorial : ℂ) * g z) :=
        funext fun k => by rw [mul_pow]; ring
      rw [e]
      exact h2
    have hI := hasSum_circleIntegral_of_dominated hR.le hcont hsum hbd hpt
    have hI2 := hI.mul_left ((ρ : ℂ) ^ i * (2 * π * I)⁻¹)
    have e1 : (fun k => s ^ k / (k.factorial : ℂ) * A k) = fun k => (ρ : ℂ) ^ i *
        (2 * π * I)⁻¹ * ∮ z in C(c, R), ((z - c) ^ (i + 1))⁻¹ *
          (s ^ k / (k.factorial : ℂ) * (ℓ z ^ k * g z)) := by
      funext k
      simp only [hA, coeff, cauchyCoeff]
      have e : (fun z => ((z - c) ^ (i + 1))⁻¹ * (s ^ k / (k.factorial : ℂ) * (ℓ z ^ k * g z))) =
          fun z => s ^ k / (k.factorial : ℂ) * (((z - c) ^ (i + 1))⁻¹ * (ℓ z ^ k * g z)) := by
        funext z; ring
      rw [e, circleIntegral.integral_const_mul]
      ring
    have e2 : coeff c R ρ i (fun z => Complex.exp (s * ℓ z) * g z) = (ρ : ℂ) ^ i * (2 * π * I)⁻¹ *
        ∮ z in C(c, R), ((z - c) ^ (i + 1))⁻¹ * (Complex.exp (s * ℓ z) * g z) := by
      unfold coeff cauchyCoeff; ring
    rw [e1, e2]
    exact hI2
  -- the series is entire
  have hentire : Differentiable ℂ fun s : ℂ => ∑' k, s ^ k / (k.factorial : ℂ) * A k := by
    intro s₀
    set r : ℝ := ‖s₀‖ + 1 with hr
    have hU : IsOpen (ball (0 : ℂ) r) := isOpen_ball
    have hdiff : ∀ k, DifferentiableOn ℂ (fun s : ℂ => s ^ k / (k.factorial : ℂ) * A k)
        (ball (0 : ℂ) r) := fun k => ((differentiableOn_id.pow k).div_const _).mul_const _
    have hbound : ∀ k, ∀ s ∈ ball (0 : ℂ) r, ‖s ^ k / (k.factorial : ℂ) * A k‖ ≤
        (r * L) ^ k / k.factorial * (G * (ρ / R) ^ i) := by
      intro k s hs
      have hs' : ‖s‖ ≤ r := (mem_ball_zero_iff.mp hs).le
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      calc ‖s‖ ^ k / k.factorial * ‖A k‖ ≤ r ^ k / k.factorial * (L ^ k * G * (ρ / R) ^ i) := by
            gcongr
            exact hAb k
        _ = (r * L) ^ k / k.factorial * (G * (ρ / R) ^ i) := by rw [mul_pow]; ring
    have hd := Complex.differentiableOn_tsum_of_summable_norm
      ((Real.summable_pow_div_factorial (r * L)).mul_right (G * (ρ / R) ^ i)) hdiff hU hbound
    have hmem : s₀ ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr (by rw [hr]; linarith)
    exact hd.differentiableAt (hU.mem_nhds hmem)
  have heq : (fun s : ℂ => coeff c R ρ i (fun z => Complex.exp (s * ℓ z) * g z)) =
      fun s => ∑' k, s ^ k / (k.factorial : ℂ) * A k := funext fun s => (hrep s).tsum_eq.symm
  rw [heq]
  exact hentire

end DiscCoefficients

namespace AnalyticMarkov

namespace System

open DiscCoefficients GeomFredholm

variable (S : System)

/-- `θ̃ = (1 + θ)/2 ∈ (θ, 1)`. -/
def θt : ℝ := (1 + S.θ) / 2

/-- The normalization ratio `ϑ = √θ̃`. -/
def ϑ : ℝ := Real.sqrt S.θt

/-- The normalization radius `ρ_a = ϑ R_a`. -/
def ρ (a : Fin S.p) : ℝ := S.ϑ * S.R a

theorem θt_pos : 0 < S.θt := by unfold θt; linarith [S.θ_nonneg]
theorem θt_lt_one : S.θt < 1 := by unfold θt; linarith [S.θ_lt_one]
theorem θ_le_θt : S.θ ≤ S.θt := by unfold θt; linarith [S.θ_lt_one]
theorem ϑ_pos : 0 < S.ϑ := Real.sqrt_pos.mpr S.θt_pos
theorem ϑ_lt_one : S.ϑ < 1 := by
  unfold ϑ; rw [Real.sqrt_lt' one_pos]; simpa using S.θt_lt_one
theorem ϑ_sq : S.ϑ ^ 2 = S.θt := Real.sq_sqrt S.θt_pos.le
theorem ρ_pos (a : Fin S.p) : 0 < S.ρ a := mul_pos S.ϑ_pos (S.R_pos a)

/-- The coefficient of a word `P` from `(a, i)` to `(b, j)`. -/
def wordEntry (s : ℂ) (P : List (Fin S.q)) (a : Fin S.p) (i : ℕ) (b : Fin S.p) (j : ℕ) : ℂ :=
  coeff (S.c a) (S.R a) (S.ρ a) i
    (fun z => Complex.exp (s * S.compΛ P z) * ((S.compφ P z - S.c b) / S.ρ b) ^ j)

/-- The words of length `m` from `a` to `b`. -/
def wordsTo (a b : Fin S.p) (m : ℕ) : Finset (List (Fin S.q)) :=
  (S.paths a m).filter fun P => S.endState a P = b

/-- The transfer matrix entry. -/
def entry (s : ℂ) (x y : Fin S.p × ℕ) : ℂ :=
  ∑ P ∈ S.wordsTo x.1 y.1 1, S.wordEntry s P x.1 x.2 y.1 y.2

instance : NeZero S.p := ⟨S.p_pos.ne'⟩

/-- `ℕ ≃ Fin p × ℕ`, `p i + a ↦ (a, i)`. -/
def decode : ℕ ≃ Fin S.p × ℕ := (Nat.divModEquiv S.p).trans (Equiv.prodComm _ _)

theorem decode_snd (m : ℕ) : (S.decode m).2 = m / S.p := by
  simp [decode, Nat.divModEquiv]

/-- The transfer matrix on `ℕ`. -/
def mat (s : ℂ) (m n : ℕ) : ℂ := S.entry s (S.decode m) (S.decode n)

variable {S}

/-! ## Bounds -/

theorem ρ_div_R (a : Fin S.p) : S.ρ a / S.R a = S.ϑ := by
  unfold ρ; field_simp [(S.R_pos a).ne']

theorem norm_image_div_le {e : Fin S.q} {z : ℂ} (hz : z ∈ S.disc (S.src e)) :
    ‖(S.φ e z - S.c (S.tgt e)) / S.ρ (S.tgt e)‖ ≤ S.ϑ := by
  have h := S.φ_maps e hz
  rw [mem_closedBall, dist_eq_norm] at h
  have hρ := S.ρ_pos (S.tgt e)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, div_le_iff₀ hρ]
  have hR := S.R_pos (S.tgt e)
  calc ‖S.φ e z - ↑(S.c (S.tgt e))‖ ≤ S.θ * S.R (S.tgt e) := h
    _ ≤ S.θt * S.R (S.tgt e) := mul_le_mul_of_nonneg_right S.θ_le_θt hR.le
    _ = S.ϑ * (S.ϑ * S.R (S.tgt e)) := by rw [← mul_assoc, ← sq, S.ϑ_sq]
    _ = S.ϑ * S.ρ (S.tgt e) := rfl

theorem mem_paths_one {a : Fin S.p} {P : List (Fin S.q)} :
    P ∈ S.paths a 1 ↔ ∃ e, P = [e] ∧ S.src e = a := by
  rw [mem_paths_succ]
  constructor
  · rintro ⟨e, P', rfl, he, hP'⟩
    simp only [paths, Finset.mem_singleton] at hP'
    exact ⟨e, by rw [hP'], he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨e, [], rfl, he, by simp [paths]⟩

theorem compφ_single (e : Fin S.q) (z : ℂ) : S.compφ [e] z = S.φ e z := rfl

theorem compΛ_single (e : Fin S.q) (z : ℂ) : S.compΛ [e] z = S.ℓ e z := by
  simp [compΛ]

/-- A uniform bound for the branch logarithms on their discs. -/
theorem exists_bound_ℓ : ∃ L : ℝ, 0 ≤ L ∧ ∀ e, ∀ z ∈ S.disc (S.src e), ‖S.ℓ e z‖ ≤ L := by
  have h : ∀ e, ∃ L, ∀ z ∈ S.disc (S.src e), ‖S.ℓ e z‖ ≤ L := fun e =>
    (isCompact_closedBall _ _).exists_bound_of_continuousOn (S.ℓ_diff e).continuousOn
  choose L hL using h
  refine ⟨∑ e, |L e|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun e z hz => ?_⟩
  calc ‖S.ℓ e z‖ ≤ L e := hL e z hz
    _ ≤ |L e| := le_abs_self _
    _ ≤ ∑ e, |L e| := Finset.single_le_sum (f := fun e => |L e|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ e)

theorem norm_entry_le {L r : ℝ} (hL : ∀ e, ∀ z ∈ S.disc (S.src e), ‖S.ℓ e z‖ ≤ L) {s : ℂ}
    (hs : ‖s‖ ≤ r) (x y : Fin S.p × ℕ) :
    ‖S.entry s x y‖ ≤ S.q * Real.exp (r * L) * S.ϑ ^ x.2 * S.ϑ ^ y.2 := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hs
  have hL0 : ∀ e, 0 ≤ L := fun e => by
    have := hL e (S.c (S.src e)) (mem_closedBall_self (S.R_pos _).le)
    exact (norm_nonneg _).trans this
  unfold entry
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ P ∈ S.wordsTo x.1 y.1 1,
      ‖S.wordEntry s P x.1 x.2 y.1 y.2‖ ≤ Real.exp (r * L) * S.ϑ ^ x.2 * S.ϑ ^ y.2 := by
    intro P hP
    simp only [wordsTo, Finset.mem_filter] at hP
    obtain ⟨hP1, hend⟩ := hP
    obtain ⟨e, rfl, he⟩ := mem_paths_one.mp hP1
    have hend' : S.tgt e = y.1 := hend
    unfold wordEntry
    have hb : ∀ z ∈ sphere (S.c x.1 : ℂ) (S.R x.1),
        ‖Complex.exp (s * S.compΛ [e] z) * ((S.compφ [e] z - S.c y.1) / S.ρ y.1) ^ y.2‖ ≤
          Real.exp (r * L) * S.ϑ ^ y.2 := by
      intro z hz
      have hzd : z ∈ S.disc (S.src e) := by rw [he]; exact sphere_subset_closedBall hz
      rw [norm_mul, compΛ_single, compφ_single, norm_pow, ← hend']
      refine mul_le_mul ?_ (pow_le_pow_left₀ (norm_nonneg _) (norm_image_div_le hzd) _)
        (by positivity) (Real.exp_pos _).le
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
      rw [norm_mul]
      exact mul_le_mul hs (hL e z hzd) (norm_nonneg _) hr0
    have h := norm_coeff_le (S.R_pos x.1) (S.ρ_pos x.1).le hb x.2
    rw [ρ_div_R] at h
    refine h.trans (le_of_eq ?_); ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((S.wordsTo x.1 y.1 1).card : ℝ) ≤ S.q := by
    have h1 : (S.wordsTo x.1 y.1 1).card ≤ (S.paths x.1 1).card := Finset.card_filter_le _ _
    have h2 : (S.paths x.1 1).card ≤ S.q := by
      simp only [paths]
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ e ∈ Finset.univ.filter (fun e => S.src e = x.1),
            ((S.paths (S.tgt e) 0).image (e :: ·)).card
          ≤ ∑ e ∈ Finset.univ.filter (fun e => S.src e = x.1), 1 :=
            Finset.sum_le_sum fun e _ => by simp [paths]
        _ ≤ S.q := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
            exact (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast h1.trans h2
  have hprod : 0 ≤ Real.exp (r * L) * S.ϑ ^ x.2 * S.ϑ ^ y.2 := by
    have := S.ϑ_pos; positivity
  calc ((S.wordsTo x.1 y.1 1).card : ℝ) * (Real.exp (r * L) * S.ϑ ^ x.2 * S.ϑ ^ y.2)
      ≤ S.q * (Real.exp (r * L) * S.ϑ ^ x.2 * S.ϑ ^ y.2) :=
        mul_le_mul_of_nonneg_right hcard hprod
    _ = S.q * Real.exp (r * L) * S.ϑ ^ x.2 * S.ϑ ^ y.2 := by ring

variable (S) in
/-- The decay rate on `ℕ`: `η = ϑ^{1/p}`. -/
def η : ℝ := S.ϑ ^ ((1 : ℝ) / S.p)

theorem η_pos : 0 < S.η := Real.rpow_pos_of_pos S.ϑ_pos _

theorem η_lt_one : S.η < 1 :=
  Real.rpow_lt_one S.ϑ_pos.le S.ϑ_lt_one (by have := S.p_pos; positivity)

theorem η_pow_p : S.η ^ S.p = S.ϑ := by
  unfold η
  rw [← Real.rpow_natCast, ← Real.rpow_mul S.ϑ_pos.le, one_div,
    inv_mul_cancel₀ (by exact_mod_cast S.p_pos.ne'), Real.rpow_one]

theorem ϑ_pow_le (m : ℕ) : S.ϑ ^ (m / S.p) ≤ S.η ^ m / S.η ^ (S.p - 1) := by
  have hη := S.η_pos
  have hη1 := S.η_lt_one
  have hdm := Nat.div_add_mod m S.p
  have hmod : m % S.p ≤ S.p - 1 := by have := Nat.mod_lt m S.p_pos; omega
  rw [le_div_iff₀ (by positivity), ← S.η_pow_p, ← pow_mul]
  calc S.η ^ (S.p * (m / S.p)) * S.η ^ (S.p - 1)
      ≤ S.η ^ (S.p * (m / S.p)) * S.η ^ (m % S.p) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1.le hmod) (by positivity)
    _ = S.η ^ m := by rw [← pow_add, hdm]

/-- **Geometric decay of the transfer matrix**, uniformly on `|s| ≤ r`. -/
theorem geomDecay_mat {L r : ℝ} (hL : ∀ e, ∀ z ∈ S.disc (S.src e), ‖S.ℓ e z‖ ≤ L)
    {s : ℂ} (hs : ‖s‖ ≤ r) :
    GeomDecay (S.mat s) (S.q * Real.exp (r * L) / (S.η ^ (S.p - 1)) ^ 2) S.η := by
  have hη := S.η_pos
  refine ⟨by positivity, hη.le, S.η_lt_one, fun m n => ?_⟩
  refine (norm_entry_le hL hs (S.decode m) (S.decode n)).trans ?_
  rw [decode_snd, decode_snd]
  have h1 := ϑ_pow_le (S := S) m
  have h2 := ϑ_pow_le (S := S) n
  have hϑ : 0 ≤ S.ϑ := S.ϑ_pos.le
  calc S.q * Real.exp (r * L) * S.ϑ ^ (m / S.p) * S.ϑ ^ (n / S.p)
      ≤ S.q * Real.exp (r * L) * (S.η ^ m / S.η ^ (S.p - 1)) * (S.η ^ n / S.η ^ (S.p - 1)) := by
        gcongr
    _ = S.q * Real.exp (r * L) / (S.η ^ (S.p - 1)) ^ 2 * S.η ^ m * S.η ^ n := by
        field_simp

/-- **The transfer matrix is entire in `s`.** -/
theorem differentiable_mat (m n : ℕ) : Differentiable ℂ fun s => S.mat s m n := by
  unfold mat entry
  refine Differentiable.fun_sum fun P hP => ?_
  simp only [wordsTo, Finset.mem_filter] at hP
  obtain ⟨e, rfl, he⟩ := mem_paths_one.mp hP.1
  unfold wordEntry
  have hsph : sphere (S.c (S.decode m).1 : ℂ) (S.R (S.decode m).1) ⊆ S.disc (S.src e) := by
    rw [he]; exact sphere_subset_closedBall
  have hℓ : ContinuousOn (S.compΛ [e]) (sphere (S.c (S.decode m).1 : ℂ) (S.R (S.decode m).1)) := by
    have := (S.ℓ_diff e).continuousOn.mono hsph
    exact this.congr fun z _ => compΛ_single e z
  have hg : ContinuousOn (fun z => ((S.compφ [e] z - S.c (S.decode n).1) / S.ρ (S.decode n).1) ^
      (S.decode n).2) (sphere (S.c (S.decode m).1 : ℂ) (S.R (S.decode m).1)) :=
    ((((S.φ_diff e).continuousOn.mono hsph).sub continuousOn_const).div_const _).pow _
  exact differentiable_coeff_exp_mul (S.R_pos _) (S.ρ_pos _).le hℓ hg _

/-! ## Sums over words -/

theorem sum_wordsTo_succ (a b : Fin S.p) (n : ℕ) (H : List (Fin S.q) → ℂ) :
    ∑ P ∈ S.wordsTo a b (n + 1), H P =
      ∑ e ∈ Finset.univ.filter (fun e => S.src e = a), ∑ P ∈ S.wordsTo (S.tgt e) b n, H (e :: P) := by
  unfold wordsTo
  rw [paths, Finset.filter_biUnion, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.filter_image, Finset.sum_image (fun x _ y _ h => List.cons_injective h)]
    rfl
  · intro e₁ _ e₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro P h1 h2
    simp only [Finset.mem_filter, Finset.mem_image] at h1 h2
    obtain ⟨⟨P₁, -, rfl⟩, -⟩ := h1
    obtain ⟨⟨P₂, -, h⟩, -⟩ := h2
    exact hne (List.cons_eq_cons.mp h).1.symm

theorem wordsTo_zero (a b : Fin S.p) :
    S.wordsTo a b 0 = if a = b then {[]} else ∅ := by
  unfold wordsTo
  split_ifs with h
  · subst h; simp [paths, endState]
  · ext P
    simp only [paths, Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false,
      not_and]
    intro hP; subst hP; exact h

theorem sum_wordsTo_one (a b : Fin S.p) (H : List (Fin S.q) → ℂ) :
    ∑ P ∈ S.wordsTo a b 1, H P =
      ∑ e ∈ Finset.univ.filter (fun e => S.src e = a ∧ S.tgt e = b), H [e] := by
  rw [sum_wordsTo_succ, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [wordsTo_zero]
  by_cases h1 : S.src e = a <;> by_cases h2 : S.tgt e = b <;> simp [h1, h2]

/-! ## The substitution step -/

theorem hasSum_wordEntry_cons (s : ℂ) {e : Fin S.q} {m : ℕ} {P : List (Fin S.q)}
    (hP : P ∈ S.paths (S.tgt e) m) (i : ℕ) (b : Fin S.p) (j : ℕ) :
    HasSum (fun l => S.wordEntry s [e] (S.src e) i (S.tgt e) l *
        S.wordEntry s P (S.tgt e) l b j) (S.wordEntry s (e :: P) (S.src e) i b j) := by
  have hR := S.R_pos (S.src e)
  have hR' := S.R_pos (S.tgt e)
  have hρ' := S.ρ_pos (S.tgt e)
  have hr0 : 0 ≤ S.θ * S.R (S.tgt e) := mul_nonneg S.θ_nonneg hR'.le
  have hr' : S.θ * S.R (S.tgt e) < S.R (S.tgt e) := by nlinarith [S.θ_lt_one]
  obtain ⟨hdφ, hdΛ⟩ := differentiableOn_compφ hP
  have hg : DifferentiableOn ℂ (fun z => Complex.exp (s * S.compΛ P z) *
      ((S.compφ P z - S.c b) / S.ρ b) ^ j) (S.disc (S.tgt e)) :=
    ((hdΛ.const_mul s).cexp).mul (((hdφ.sub_const _).div_const _).pow _)
  have hφ : ContinuousOn (S.φ e) (sphere (S.c (S.src e) : ℂ) (S.R (S.src e))) :=
    (S.φ_diff e).continuousOn.mono sphere_subset_closedBall
  have hφm : MapsTo (S.φ e) (sphere (S.c (S.src e) : ℂ) (S.R (S.src e)))
      (closedBall (S.c (S.tgt e) : ℂ) (S.θ * S.R (S.tgt e))) :=
    (S.φ_maps e).mono_left sphere_subset_closedBall
  have hw : ContinuousOn (fun z => Complex.exp (s * S.ℓ e z))
      (sphere (S.c (S.src e) : ℂ) (S.R (S.src e))) :=
    (((S.ℓ_diff e).continuousOn.mono sphere_subset_closedBall).const_smul s).cexp
  have h := hasSum_coeff_comp (ρ := S.ρ (S.src e)) hR hR' hρ' hr0 hr' hg hφ hφm hw i
  unfold wordEntry
  simp only [compΛ_single, compφ_single]
  have e1 : (fun z => Complex.exp (s * S.ℓ e z) * (fun z => Complex.exp (s * S.compΛ P z) *
      ((S.compφ P z - S.c b) / S.ρ b) ^ j) (S.φ e z)) = fun z =>
        Complex.exp (s * S.compΛ (e :: P) z) * ((S.compφ (e :: P) z - S.c b) / S.ρ b) ^ j := by
    funext z
    rw [compΛ_cons, compφ_cons, mul_add, Complex.exp_add]
    ring
  simp only [e1] at h
  exact h

/-! ## Powers of the transfer matrix -/

theorem summable_mat_mul_ipow (s : ℂ) (m : ℕ) (X Y : ℕ) :
    Summable fun k => S.mat s X k * ipow (S.mat s) (m + 1) k Y := by
  obtain ⟨L, -, hL⟩ := S.exists_bound_ℓ
  have hM := geomDecay_mat (S := S) hL (r := ‖s‖) le_rfl
  set C := S.q * Real.exp (‖s‖ * L) / (S.η ^ (S.p - 1)) ^ 2
  have hC := hM.const_nonneg
  have hS := (sqSum_pos S.η_pos.le S.η_lt_one).le
  refine Summable.of_norm_bounded
    (hM.summable_mul (C * S.η ^ X) (C * (C * sqSum S.η) ^ m * S.η ^ Y)) fun k => ?_
  rw [norm_mul]
  calc ‖S.mat s X k‖ * ‖ipow (S.mat s) (m + 1) k Y‖
      ≤ (C * S.η ^ X * S.η ^ k) * (C * (C * sqSum S.η) ^ m * S.η ^ k * S.η ^ Y) :=
        mul_le_mul (hM.bound X k) (norm_ipow_succ_le hM m k Y) (norm_nonneg _)
          (le_trans (norm_nonneg _) (hM.bound X k))
    _ = C * S.η ^ X * S.η ^ k * (C * (C * sqSum S.η) ^ m * S.η ^ Y * S.η ^ k) := by ring

/-- **The entries of the matrix powers are sums over admissible words.** -/
theorem ipow_mat_decode (s : ℂ) (m : ℕ) (x y : Fin S.p × ℕ) :
    ipow (S.mat s) (m + 1) (S.decode.symm x) (S.decode.symm y) =
      ∑ P ∈ S.wordsTo x.1 y.1 (m + 1), S.wordEntry s P x.1 x.2 y.1 y.2 := by
  induction m generalizing x with
  | zero =>
    rw [ipow_one]
    simp only [mat, Equiv.apply_symm_apply, entry]
  | succ m ih =>
    have hdef : ipow (S.mat s) (m + 1 + 1) (S.decode.symm x) (S.decode.symm y) =
        ∑' k, S.mat s (S.decode.symm x) k * ipow (S.mat s) (m + 1) k (S.decode.symm y) := rfl
    rw [hdef, ← S.decode.symm.tsum_eq]
    have hsum : Summable fun c : Fin S.p × ℕ => S.mat s (S.decode.symm x) (S.decode.symm c) *
        ipow (S.mat s) (m + 1) (S.decode.symm c) (S.decode.symm y) :=
      (Equiv.summable_iff (f := fun k => S.mat s (S.decode.symm x) k *
        ipow (S.mat s) (m + 1) k (S.decode.symm y)) S.decode.symm).mpr
        (summable_mat_mul_ipow (S := S) s m (S.decode.symm x) (S.decode.symm y))
    rw [hsum.tsum_prod, tsum_fintype]
    simp only [mat, Equiv.apply_symm_apply]
    simp_rw [ih]
    -- each state `c'` contributes the words through `c'`
    have hstate : ∀ c' : Fin S.p, (∑' l, S.entry s x (c', l) *
        ∑ P ∈ S.wordsTo c' y.1 (m + 1), S.wordEntry s P c' l y.1 y.2) =
        ∑ e ∈ Finset.univ.filter (fun e => S.src e = x.1 ∧ S.tgt e = c'),
          ∑ P ∈ S.wordsTo c' y.1 (m + 1), S.wordEntry s (e :: P) x.1 x.2 y.1 y.2 := by
      intro c'
      simp only [entry]
      simp_rw [sum_wordsTo_one, Finset.sum_mul_sum]
      rw [Summable.tsum_finsetSum]
      · refine Finset.sum_congr rfl fun e he => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        rw [Summable.tsum_finsetSum]
        · refine Finset.sum_congr rfl fun P hP => ?_
          simp only [wordsTo, Finset.mem_filter] at hP
          have h := hasSum_wordEntry_cons (S := S) s (e := e) (by rw [he.2]; exact hP.1) x.2 y.1 y.2
          rw [he.1, he.2] at h
          exact h.tsum_eq
        · intro P hP
          simp only [wordsTo, Finset.mem_filter] at hP
          have h := hasSum_wordEntry_cons (S := S) s (e := e) (by rw [he.2]; exact hP.1) x.2 y.1 y.2
          rw [he.1, he.2] at h
          exact h.summable
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        refine summable_sum fun P hP => ?_
        simp only [wordsTo, Finset.mem_filter] at hP
        have h := hasSum_wordEntry_cons (S := S) s (e := e) (by rw [he.2]; exact hP.1) x.2 y.1 y.2
        rw [he.1, he.2] at h
        exact h.summable
    simp_rw [hstate]
    rw [sum_wordsTo_succ]
    -- regroup by the target state of the first branch
    rw [Finset.sum_comm' (t' := Finset.univ.filter (fun e => S.src e = x.1))
      (s' := fun e => {S.tgt e})]
    · refine Finset.sum_congr rfl fun e _ => ?_
      simp
    · intro c' e
      simp only [Finset.mem_univ, Finset.mem_filter, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact ⟨h.2.symm, h.1⟩
      · intro h; exact ⟨h.2, h.1.symm⟩

/-! ## The trace formula -/

/-- `Σ_{closed words P of length n} e^{sΛ_P}/(1 − e^{Λ_P})`. -/
def cycleTraceSum (s : ℂ) (n : ℕ) : ℂ :=
  ∑ a, ∑ P ∈ S.wordsTo a a n,
    Complex.exp (s * S.cycleΛ a n P) / (1 - Complex.exp (S.cycleΛ a n P))

theorem isClosed_of_mem_wordsTo {a : Fin S.p} {n : ℕ} {P : List (Fin S.q)}
    (hP : P ∈ S.wordsTo a a (n + 1)) : S.IsClosed a (n + 1) P := by
  simp only [wordsTo, Finset.mem_filter] at hP
  exact ⟨hP.1, hP.2, Nat.succ_ne_zero n⟩

theorem hasSum_wordEntry_diag (s : ℂ) {a : Fin S.p} {n : ℕ} {P : List (Fin S.q)}
    (hP : P ∈ S.wordsTo a a (n + 1)) :
    HasSum (fun i => S.wordEntry s P a i a i)
      (Complex.exp (s * S.cycleΛ a (n + 1) P) / (1 - Complex.exp (S.cycleΛ a (n + 1) P))) := by
  have hcl := isClosed_of_mem_wordsTo hP
  obtain ⟨hmem, hfix, -, -⟩ := fixPt_spec hcl
  have hspec := cycleΛ_spec hcl
  obtain ⟨hdφ, hdΛ⟩ := differentiableOn_compφ hcl.1
  have hmaps := (mapsTo_compφ hcl.1).2 hcl.2.2
  rw [hcl.2.1] at hmaps
  have h := hasSum_coeff_diag (ρ := S.ρ a) (S.R_pos a) (S.ρ_pos a) S.θ_nonneg S.θ_lt_one hdφ
    hmaps ((hdΛ.const_mul s).cexp) (S.mem_ball_of_mem_θ hmem) hfix
  unfold cycleΛ at hspec ⊢
  rw [hspec.2.2] at h
  exact h

theorem summable_ipow_diag (s : ℂ) (m : ℕ) :
    Summable fun k => ipow (S.mat s) (m + 1) k k := by
  obtain ⟨L, -, hL⟩ := S.exists_bound_ℓ
  have hM := geomDecay_mat (S := S) hL (r := ‖s‖) le_rfl
  set C := S.q * Real.exp (‖s‖ * L) / (S.η ^ (S.p - 1)) ^ 2
  refine Summable.of_norm_bounded (hM.summable_mul (C * (C * sqSum S.η) ^ m) 1) fun k => ?_
  exact (norm_ipow_succ_le hM m k k).trans (le_of_eq (by ring))

/-- **The trace formula.** -/
theorem itrace_mat (s : ℂ) (m : ℕ) : itrace (S.mat s) (m + 1) = S.cycleTraceSum s (m + 1) := by
  unfold itrace cycleTraceSum
  rw [← S.decode.symm.tsum_eq]
  have hsum : Summable fun c : Fin S.p × ℕ =>
      ipow (S.mat s) (m + 1) (S.decode.symm c) (S.decode.symm c) :=
    (Equiv.summable_iff (f := fun k => ipow (S.mat s) (m + 1) k k) S.decode.symm).mpr
      (summable_ipow_diag (S := S) s m)
  rw [hsum.tsum_prod, tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [ipow_mat_decode]
  rw [Summable.tsum_finsetSum fun P hP => (hasSum_wordEntry_diag (S := S) s hP).summable]
  exact Finset.sum_congr rfl fun P hP => (hasSum_wordEntry_diag (S := S) s hP).tsum_eq

end System

end AnalyticMarkov

end GaloisForLFunctions.HTGeometry

end
