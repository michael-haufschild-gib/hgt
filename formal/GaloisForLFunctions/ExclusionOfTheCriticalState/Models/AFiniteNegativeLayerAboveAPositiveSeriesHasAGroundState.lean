import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A finite negative layer above a positive series has a ground state

In a separable real Hilbert space `E` consider the quadratic energy

  `𝓔(F) = Σ_j w_j (⟪a_j, F⟫² + ⟪b_j, F⟫²) + Σ_k v_k ⟪p_k, F⟫ ⟪q_k, F⟫`,

a nonnegative series (`w_j ≥ 0`) plus a finite-rank form (`k` over a finite type). It is the shape of a confined
zero-side form: the on-line zeros give squares `|L F(iγ)|²`, the finitely many off-line zeros give
products `L F(z) L F(−z)`. If `𝓔` takes a negative value on an admissible vector (series summable), it
attains its minimum `λ < 0` on the unit sphere (`exists_groundState_of_negative`): there is a unit
admissible `F*` with `𝓔(F*) = λ` and `𝓔(G) ≥ λ ‖G‖²` for every admissible `G`. The ground state
satisfies the Euler–Lagrange equation `𝓔(F*, G) = λ ⟪F*, G⟫` for every admissible `G`
(`pair_eq_of_groundState`); for a finite series it is the explicit combination
`F* = λ⁻¹ (Σ_j w_j (⟪a_j, F*⟫ a_j + ⟪b_j, F*⟫ b_j) + Σ_k v_k (⟪p_k, F*⟫ q_k + ⟪q_k, F*⟫ p_k)/2)`
(`eq_inv_smul_rieszVec_of_groundState`, `mem_span_of_groundState`).

Mechanism. A minimizing sequence on the unit sphere has a weakly convergent subsequence
(Fréchet–Riesz and sequential Banach–Alaoglu); the finite-rank part converges along it, the
series is weakly lower semicontinuous term by term, so the weak limit `F` has `𝓔(F) ≤ λ < 0` and
`‖F‖ ≤ 1`; hence `F ≠ 0` and `F/‖F‖` attains `λ`.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.GroundState

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

/-- Every norm-bounded sequence in a separable real Hilbert space has a weakly convergent
subsequence whose limit obeys the same bound. -/
theorem exists_weaklyConvergent_subseq [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ w : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ‖w‖ ≤ M ∧
      ∀ y : E, Tendsto (fun n => ⟪u (φ n), y⟫) atTop (𝓝 ⟪w, y⟫) := by
  let d : ℕ → WeakDual ℝ E := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (u n))
  let S : Set (WeakDual ℝ E) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 M
  have hd : ∀ n, d n ∈ S := by
    intro n
    change dist (WeakDual.toStrongDual (d n)) 0 ≤ M
    rw [dist_zero_right]
    change ‖InnerProductSpace.toDual ℝ E (u n)‖ ≤ M
    rw [(InnerProductSpace.toDual ℝ E).norm_map]
    exact hM n
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E 0 M).subseq_of_frequently_in
    (Eventually.of_forall hd).frequently
  let w : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual a)
  have hw : ‖w‖ ≤ M := by
    have ha' : dist (WeakDual.toStrongDual a) 0 ≤ M := ha
    rw [dist_zero_right] at ha'
    change ‖(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual a)‖ ≤ M
    rwa [(InnerProductSpace.toDual ℝ E).symm.norm_map]
  refine ⟨w, φ, hφ, hw, fun y => ?_⟩
  have heval := (WeakDual.eval_continuous y).tendsto a |>.comp hlim
  have hwval : ⟪w, y⟫ = a y := by
    change ⟪(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual a), y⟫ = _
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  rw [hwval]
  convert heval using 1
  rfl

/-- The data of a confined energy: a positive series indexed by `ι` and a finite-rank layer
indexed by `κ`. -/
structure LayeredEnergy (E ι κ : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  w : ι → ℝ
  a : ι → E
  b : ι → E
  w_nonneg : ∀ j, 0 ≤ w j
  v : κ → ℝ
  p : κ → E
  q : κ → E

namespace LayeredEnergy

variable {ι κ : Type*} (L : LayeredEnergy E ι κ)

/-- One term of the positive series. -/
def term (F : E) (j : ι) : ℝ := L.w j * (⟪L.a j, F⟫ ^ 2 + ⟪L.b j, F⟫ ^ 2)

/-- A vector is admissible when the positive series converges at it. -/
def Admissible (F : E) : Prop := Summable (L.term F)

/-- The positive series. -/
def series (F : E) : ℝ := ∑' j, L.term F j

/-- The finite-rank layer. -/
def layer [Fintype κ] (F : E) : ℝ := ∑ k, L.v k * (⟪L.p k, F⟫ * ⟪L.q k, F⟫)

/-- The energy. -/
def energy [Fintype κ] (F : E) : ℝ := L.series F + L.layer F

theorem term_nonneg (F : E) (j : ι) : 0 ≤ L.term F j :=
  mul_nonneg (L.w_nonneg j) (by positivity)

theorem series_nonneg (F : E) : 0 ≤ L.series F := tsum_nonneg (L.term_nonneg F)

theorem term_smul (c : ℝ) (F : E) (j : ι) : L.term (c • F) j = c ^ 2 * L.term F j := by
  unfold term
  rw [inner_smul_right, inner_smul_right]
  ring

theorem admissible_smul {F : E} (hF : L.Admissible F) (c : ℝ) : L.Admissible (c • F) := by
  unfold Admissible
  rw [show L.term (c • F) = fun j => c ^ 2 * L.term F j from funext (L.term_smul c F)]
  exact hF.mul_left _

theorem series_smul (c : ℝ) (F : E) : L.series (c • F) = c ^ 2 * L.series F := by
  unfold series
  simp_rw [L.term_smul]
  exact tsum_mul_left

theorem layer_smul [Fintype κ] (c : ℝ) (F : E) : L.layer (c • F) = c ^ 2 * L.layer F := by
  unfold layer
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, inner_smul_right]
  ring

theorem energy_smul [Fintype κ] (c : ℝ) (F : E) : L.energy (c • F) = c ^ 2 * L.energy F := by
  unfold energy
  rw [L.series_smul, L.layer_smul]
  ring

theorem energy_zero [Fintype κ] : L.energy 0 = 0 := by
  have h := L.energy_smul 0 0
  rw [zero_smul] at h
  rw [h]; ring

/-- The constant bounding the layer: `|layer F| ≤ C ‖F‖²`. -/
def layerConst [Fintype κ] : ℝ := ∑ k, |L.v k| * (‖L.p k‖ * ‖L.q k‖)

theorem abs_layer_le [Fintype κ] (F : E) : |L.layer F| ≤ L.layerConst * ‖F‖ ^ 2 := by
  unfold layer layerConst
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := abs_real_inner_le_norm (L.p k) F
  have h2 := abs_real_inner_le_norm (L.q k) F
  calc |L.v k| * (|⟪L.p k, F⟫| * |⟪L.q k, F⟫|)
      ≤ |L.v k| * ((‖L.p k‖ * ‖F‖) * (‖L.q k‖ * ‖F‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) (abs_nonneg _)
    _ = |L.v k| * (‖L.p k‖ * ‖L.q k‖) * ‖F‖ ^ 2 := by ring

theorem energy_ge [Fintype κ] (F : E) : -(L.layerConst * ‖F‖ ^ 2) ≤ L.energy F := by
  unfold energy
  have := L.abs_layer_le F
  have := L.series_nonneg F
  linarith [neg_abs_le (L.layer F)]

/-- The layer is continuous along weakly convergent sequences. -/
theorem tendsto_layer [Fintype κ] {u : ℕ → E} {F : E}
    (hu : ∀ y : E, Tendsto (fun n => ⟪u n, y⟫) atTop (𝓝 ⟪F, y⟫)) :
    Tendsto (fun n => L.layer (u n)) atTop (𝓝 (L.layer F)) := by
  unfold layer
  refine tendsto_finsetSum _ fun k _ => ?_
  have hp : Tendsto (fun n => ⟪L.p k, u n⟫) atTop (𝓝 ⟪L.p k, F⟫) := by
    rw [real_inner_comm F (L.p k)]; exact (hu (L.p k)).congr fun n => real_inner_comm (L.p k) (u n)
  have hq : Tendsto (fun n => ⟪L.q k, u n⟫) atTop (𝓝 ⟪L.q k, F⟫) := by
    rw [real_inner_comm F (L.q k)]; exact (hu (L.q k)).congr fun n => real_inner_comm (L.q k) (u n)
  exact (hp.mul hq).const_mul _

/-- **The positive series is weakly lower semicontinuous.** If `u_n ⇀ F` and the series at `u_n`
tend to `s`, then the series converges at `F` with value at most `s`. -/
theorem admissible_and_series_le_of_tendsto {u : ℕ → E} {F : E}
    (hu : ∀ y : E, Tendsto (fun n => ⟪u n, y⟫) atTop (𝓝 ⟪F, y⟫))
    (hadm : ∀ n, L.Admissible (u n)) {s : ℝ}
    (hs : Tendsto (fun n => L.series (u n)) atTop (𝓝 s)) :
    L.Admissible F ∧ L.series F ≤ s := by
  have hterm : ∀ j, Tendsto (fun n => L.term (u n) j) atTop (𝓝 (L.term F j)) := by
    intro j
    have ha : Tendsto (fun n => ⟪L.a j, u n⟫) atTop (𝓝 ⟪L.a j, F⟫) := by
      rw [real_inner_comm F (L.a j)]; exact (hu (L.a j)).congr fun n => real_inner_comm (L.a j) (u n)
    have hb : Tendsto (fun n => ⟪L.b j, u n⟫) atTop (𝓝 ⟪L.b j, F⟫) := by
      rw [real_inner_comm F (L.b j)]; exact (hu (L.b j)).congr fun n => real_inner_comm (L.b j) (u n)
    exact ((ha.pow 2).add (hb.pow 2)).const_mul _
  have hpart : ∀ N : Finset ι, ∑ j ∈ N, L.term F j ≤ s := by
    intro N
    have hlim := tendsto_finsetSum N fun j _ => hterm j
    refine le_of_tendsto_of_tendsto' hlim hs fun n => ?_
    exact (hadm n).sum_le_tsum N (fun j _ => L.term_nonneg _ j)
  have hsum : L.Admissible F := summable_of_sum_le (L.term_nonneg F) hpart
  exact ⟨hsum, Real.tsum_le_of_sum_le (L.term_nonneg F) hpart⟩

/-- **Ground state.** If the energy is negative at some admissible vector, it attains its minimum
`λ < 0` over the admissible unit sphere at a unit vector `F*`, and `𝓔(G) ≥ λ ‖G‖²` for every
admissible `G`. -/
theorem exists_groundState_of_negative [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [Fintype κ] {F₀ : E} (hF₀ : L.Admissible F₀) (hneg : L.energy F₀ < 0) :
    ∃ F : E, L.Admissible F ∧ ‖F‖ = 1 ∧ L.energy F < 0 ∧
      ∀ G : E, L.Admissible G → L.energy F * ‖G‖ ^ 2 ≤ L.energy G := by
  set S : Set ℝ := {x | ∃ F : E, L.Admissible F ∧ ‖F‖ = 1 ∧ L.energy F = x}
  have hF₀ne : F₀ ≠ 0 := by intro h; rw [h, L.energy_zero] at hneg; exact lt_irrefl _ hneg
  have hn₀ : 0 < ‖F₀‖ := norm_pos_iff.mpr hF₀ne
  -- the normalized starting vector
  have hunit : ∀ G : E, G ≠ 0 → ‖(‖G‖⁻¹ : ℝ) • G‖ = 1 := fun G hG => by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hG)]
  have henergy_unit : ∀ G : E, G ≠ 0 → L.energy ((‖G‖⁻¹ : ℝ) • G) = L.energy G / ‖G‖ ^ 2 :=
    fun G hG => by
      rw [L.energy_smul, inv_pow, div_eq_inv_mul]
  have hS : S.Nonempty := ⟨_, (‖F₀‖⁻¹ : ℝ) • F₀, L.admissible_smul hF₀ _, hunit F₀ hF₀ne, rfl⟩
  have hSb : BddBelow S := ⟨-L.layerConst, by
    rintro x ⟨F, -, hF1, rfl⟩
    have := L.energy_ge F
    rwa [hF1, one_pow, mul_one] at this⟩
  set lam := sInf S
  have hlam : lam < 0 := by
    have h1 : lam ≤ L.energy F₀ / ‖F₀‖ ^ 2 :=
      csInf_le hSb ⟨_, L.admissible_smul hF₀ _, hunit F₀ hF₀ne, henergy_unit F₀ hF₀ne⟩
    have h2 : L.energy F₀ / ‖F₀‖ ^ 2 < 0 := div_neg_of_neg_of_pos hneg (by positivity)
    linarith
  have hle : ∀ G : E, L.Admissible G → lam * ‖G‖ ^ 2 ≤ L.energy G := by
    intro G hG
    by_cases hG0 : G = 0
    · rw [hG0, norm_zero, L.energy_zero]; simp
    · have hm := csInf_le hSb ⟨_, L.admissible_smul hG _, hunit G hG0, henergy_unit G hG0⟩
      have hpos : 0 < ‖G‖ ^ 2 := by positivity
      rw [le_div_iff₀ hpos] at hm
      exact hm
  -- a minimizing sequence
  obtain ⟨x, -, hx, hxS⟩ := exists_seq_tendsto_sInf hS hSb
  choose u hu_adm hu_norm hu_val using hxS
  obtain ⟨F, φ, hφ, hF1, hweak⟩ := exists_weaklyConvergent_subseq u 1 (fun n => (hu_norm n).le)
  have hlay := L.tendsto_layer hweak
  have hE : Tendsto (fun n => L.energy (u (φ n))) atTop (𝓝 lam) := by
    simp_rw [hu_val]; exact hx.comp hφ.tendsto_atTop
  have hser : Tendsto (fun n => L.series (u (φ n))) atTop (𝓝 (lam - L.layer F)) := by
    have := hE.sub hlay
    refine this.congr fun n => ?_
    unfold energy; ring
  obtain ⟨hFadm, hFser⟩ := L.admissible_and_series_le_of_tendsto hweak (fun n => hu_adm _) hser
  have hEF : L.energy F ≤ lam := by unfold energy; linarith
  have hF0 : F ≠ 0 := by
    intro h; rw [h, L.energy_zero] at hEF; linarith
  have hnF : 0 < ‖F‖ := norm_pos_iff.mpr hF0
  set F' := (‖F‖⁻¹ : ℝ) • F
  have hF'adm : L.Admissible F' := L.admissible_smul hFadm _
  have hF'n : ‖F'‖ = 1 := hunit F hF0
  have hF'E : L.energy F' = lam := by
    have hge : lam ≤ L.energy F' := by
      have := hle F' hF'adm; rwa [hF'n, one_pow, mul_one] at this
    have hle' : L.energy F' ≤ lam := by
      rw [henergy_unit F hF0, div_le_iff₀ (by positivity)]
      have hsq : ‖F‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith
    linarith
  refine ⟨F', hF'adm, hF'n, by rw [hF'E]; exact hlam, fun G hG => ?_⟩
  rw [hF'E]
  exact hle G hG

/-! ### The polar form and the Euler–Lagrange equation -/

/-- If ˋA t + B t² ≥ 0ˋ for every real ˋtˋ, then ˋA = 0ˋ. -/
theorem eq_zero_of_forall_linear_add_sq_nonneg {A B : ℝ} (h : ∀ t : ℝ, 0 ≤ A * t + B * t ^ 2) :
    A = 0 := by
  by_contra hA
  have hpos : 0 < |A| := abs_pos.mpr hA
  set s := |A| / (2 * (|B| + 1)) with hs_def
  have hs : 0 < s := by positivity
  have h1 := h s
  have h2 := h (-s)
  have hAs : |A| * s ≤ |B| * s ^ 2 := by
    have hB : B * s ^ 2 ≤ |B| * s ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
    rcases le_or_gt 0 A with hA0 | hA0
    · rw [abs_of_nonneg hA0]; nlinarith
    · rw [abs_of_neg hA0]; nlinarith
  have hle : |A| ≤ |B| * s := by
    have : |A| * s ≤ (|B| * s) * s := by nlinarith
    exact le_of_mul_le_mul_right this hs
  have hlt : |B| * s < |A| := by
    rw [hs_def, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg B]
  linarith

/-- The polar form of the energy. -/
def pair [Fintype κ] (F G : E) : ℝ :=
  (∑' j, L.w j * (⟪L.a j, F⟫ * ⟪L.a j, G⟫ + ⟪L.b j, F⟫ * ⟪L.b j, G⟫)) +
    ∑ k, L.v k * ((⟪L.p k, F⟫ * ⟪L.q k, G⟫ + ⟪L.q k, F⟫ * ⟪L.p k, G⟫) / 2)

theorem summable_cross {F G : E} (hF : L.Admissible F) (hG : L.Admissible G) :
    Summable fun j => L.w j * (⟪L.a j, F⟫ * ⟪L.a j, G⟫ + ⟪L.b j, F⟫ * ⟪L.b j, G⟫) := by
  refine Summable.of_norm_bounded ((hF.add hG).div_const 2) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (L.w_nonneg j)]
  unfold term
  have h1 := abs_add_le (⟪L.a j, F⟫ * ⟪L.a j, G⟫) (⟪L.b j, F⟫ * ⟪L.b j, G⟫)
  rw [abs_mul, abs_mul] at h1
  have h2 : |⟪L.a j, F⟫| * |⟪L.a j, G⟫| ≤ (⟪L.a j, F⟫ ^ 2 + ⟪L.a j, G⟫ ^ 2) / 2 := by
    nlinarith [sq_nonneg (|⟪L.a j, F⟫| - |⟪L.a j, G⟫|), sq_abs ⟪L.a j, F⟫, sq_abs ⟪L.a j, G⟫]
  have h3 : |⟪L.b j, F⟫| * |⟪L.b j, G⟫| ≤ (⟪L.b j, F⟫ ^ 2 + ⟪L.b j, G⟫ ^ 2) / 2 := by
    nlinarith [sq_nonneg (|⟪L.b j, F⟫| - |⟪L.b j, G⟫|), sq_abs ⟪L.b j, F⟫, sq_abs ⟪L.b j, G⟫]
  have hw := L.w_nonneg j
  calc L.w j * |⟪L.a j, F⟫ * ⟪L.a j, G⟫ + ⟪L.b j, F⟫ * ⟪L.b j, G⟫|
      ≤ L.w j * ((⟪L.a j, F⟫ ^ 2 + ⟪L.a j, G⟫ ^ 2) / 2 + (⟪L.b j, F⟫ ^ 2 + ⟪L.b j, G⟫ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (h1.trans (add_le_add h2 h3)) hw
    _ = (L.w j * (⟪L.a j, F⟫ ^ 2 + ⟪L.b j, F⟫ ^ 2) + L.w j * (⟪L.a j, G⟫ ^ 2 + ⟪L.b j, G⟫ ^ 2)) / 2 := by
        ring

theorem admissible_add_smul {F G : E} (hF : L.Admissible F) (hG : L.Admissible G) (t : ℝ) :
    L.Admissible (F + t • G) := by
  unfold Admissible
  have e : L.term (F + t • G) = fun j => L.term F j +
      2 * t * (L.w j * (⟪L.a j, F⟫ * ⟪L.a j, G⟫ + ⟪L.b j, F⟫ * ⟪L.b j, G⟫)) + t ^ 2 * L.term G j := by
    funext j
    unfold term
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
    ring
  rw [e]
  exact (hF.add ((L.summable_cross hF hG).mul_left (2 * t))).add (hG.mul_left _)

/-- **Expansion of the energy along a line.** -/
theorem energy_add_smul [Fintype κ] {F G : E} (hF : L.Admissible F) (hG : L.Admissible G) (t : ℝ) :
    L.energy (F + t • G) = L.energy F + 2 * t * L.pair F G + t ^ 2 * L.energy G := by
  have e : L.term (F + t • G) = fun j => L.term F j +
      2 * t * (L.w j * (⟪L.a j, F⟫ * ⟪L.a j, G⟫ + ⟪L.b j, F⟫ * ⟪L.b j, G⟫)) + t ^ 2 * L.term G j := by
    funext j
    unfold term
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
    ring
  have hs : L.series (F + t • G) = L.series F +
      2 * t * (∑' j, L.w j * (⟪L.a j, F⟫ * ⟪L.a j, G⟫ + ⟪L.b j, F⟫ * ⟪L.b j, G⟫)) +
        t ^ 2 * L.series G := by
    unfold series
    rw [e, Summable.tsum_add (hF.add ((L.summable_cross hF hG).mul_left (2 * t))) (hG.mul_left _),
      Summable.tsum_add hF ((L.summable_cross hF hG).mul_left (2 * t)), tsum_mul_left, tsum_mul_left]
  have hl : L.layer (F + t • G) = L.layer F +
      2 * t * (∑ k, L.v k * ((⟪L.p k, F⟫ * ⟪L.q k, G⟫ + ⟪L.q k, F⟫ * ⟪L.p k, G⟫) / 2)) +
        t ^ 2 * L.layer G := by
    unfold layer
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
    ring
  unfold energy pair
  rw [hs, hl]
  ring

/-- **Euler–Lagrange equation.** At a ground state ˋFˋ of energy ˋλ ‖F‖²ˋ the polar form is
ˋλˋ times the inner product against every admissible vector. -/
theorem pair_eq_of_groundState [Fintype κ] {F : E} {lam : ℝ} (hF : L.Admissible F)
    (hE : L.energy F = lam * ‖F‖ ^ 2) (hmin : ∀ G, L.Admissible G → lam * ‖G‖ ^ 2 ≤ L.energy G)
    {G : E} (hG : L.Admissible G) : L.pair F G = lam * ⟪F, G⟫ := by
  have h : ∀ t : ℝ, 0 ≤ (2 * (L.pair F G - lam * ⟪F, G⟫)) * t +
      (L.energy G - lam * ‖G‖ ^ 2) * t ^ 2 := by
    intro t
    have h1 := hmin _ (L.admissible_add_smul hF hG t)
    rw [L.energy_add_smul hF hG t, hE] at h1
    have hn : ‖F + t • G‖ ^ 2 = ‖F‖ ^ 2 + 2 * t * ⟪F, G⟫ + t ^ 2 * ‖G‖ ^ 2 := by
      rw [@norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [hn] at h1
    nlinarith
  have := eq_zero_of_forall_linear_add_sq_nonneg h
  linarith

/-- The Riesz vector of the polar form (finite series). -/
def rieszVec [Fintype ι] [Fintype κ] (F : E) : E :=
  (∑ j, L.w j • (⟪L.a j, F⟫ • L.a j + ⟪L.b j, F⟫ • L.b j)) +
    ∑ k, (L.v k / 2) • (⟪L.p k, F⟫ • L.q k + ⟪L.q k, F⟫ • L.p k)

theorem pair_eq_inner_rieszVec [Fintype ι] [Fintype κ] (F G : E) :
    L.pair F G = ⟪L.rieszVec F, G⟫ := by
  unfold pair rieszVec
  rw [tsum_fintype, inner_add_left, sum_inner, sum_inner]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring

/-- **Closed form of a ground state for a finite series.** Every vector is admissible, and a ground
state of energy ˋλ ‖F‖²ˋ with ˋλ ≠ 0ˋ is the combination ˋF = λ⁻¹ R(F)ˋ of the finitely many vectors
ˋa_j, b_j, p_k, q_kˋ with its own coordinates as coefficients. -/
theorem eq_inv_smul_rieszVec_of_groundState [Fintype ι] [Fintype κ] {F : E} {lam : ℝ}
    (hlam : lam ≠ 0) (hE : L.energy F = lam * ‖F‖ ^ 2)
    (hmin : ∀ G, L.Admissible G → lam * ‖G‖ ^ 2 ≤ L.energy G) :
    F = lam⁻¹ • L.rieszVec F := by
  have hadm : ∀ G : E, L.Admissible G := fun G => Summable.of_finite
  have h : ∀ G, ⟪L.rieszVec F - lam • F, G⟫ = 0 := fun G => by
    rw [inner_sub_left, real_inner_smul_left, ← L.pair_eq_inner_rieszVec,
      L.pair_eq_of_groundState (hadm F) hE hmin (hadm G)]
    ring
  have h0 : L.rieszVec F - lam • F = 0 := by
    have := h (L.rieszVec F - lam • F)
    rwa [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at this
  rw [sub_eq_zero] at h0
  rw [h0, smul_smul, inv_mul_cancel₀ hlam, one_smul]

/-- **A finite ground state is a finite combination of the defining vectors.** -/
theorem mem_span_of_groundState [Finite ι] [Fintype κ] {F : E} {lam : ℝ} (hlam : lam ≠ 0)
    (hE : L.energy F = lam * ‖F‖ ^ 2)
    (hmin : ∀ G, L.Admissible G → lam * ‖G‖ ^ 2 ≤ L.energy G) :
    F ∈ Submodule.span ℝ (Set.range L.a ∪ Set.range L.b ∪ Set.range L.p ∪ Set.range L.q) := by
  letI : Fintype ι := Fintype.ofFinite ι
  rw [L.eq_inv_smul_rieszVec_of_groundState hlam hE hmin]
  refine Submodule.smul_mem _ _ ?_
  have hmem : ∀ x ∈ Set.range L.a ∪ Set.range L.b ∪ Set.range L.p ∪ Set.range L.q,
      x ∈ Submodule.span ℝ (Set.range L.a ∪ Set.range L.b ∪ Set.range L.p ∪ Set.range L.q) :=
    fun x hx => Submodule.subset_span hx
  unfold rieszVec
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem _ ?_)) (Submodule.smul_mem _ _ (hmem _ ?_))))
    (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem _ ?_)) (Submodule.smul_mem _ _ (hmem _ ?_))))
  · exact Or.inl (Or.inl (Or.inl ⟨j, rfl⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨j, rfl⟩))
  · exact Or.inr ⟨k, rfl⟩
  · exact Or.inl (Or.inr ⟨k, rfl⟩)

end LayeredEnergy

end GaloisForLFunctions.ExclusionOfTheCriticalState.GroundState
