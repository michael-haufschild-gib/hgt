import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheCanonicalClassOfAWindow

/-!
# The window Dirichlet algebra

A window of length `A` is the interval `[−A, 0]` of the scaling line; its **module** `F_A` is the
space of real functions vanishing off it (`windowSupported`). The fold of a window by `t ≥ 0` is the
**window shift** `(T_t H)(u) = 1_{u ≤ 0} H(u − t)`: translation toward the right end, cut at the
end. Window shifts compose exactly and die past the length:

* `T_s T_t = T_{s+t}` for `s ≥ 0` (`windowShift_add`), `T_0 = 1` and `T_t = 0` for `t > A` on `F_A`
  (`windowShift_zero`, `windowShift_eq_zero`).

So the Hecke shifts `n^{−1/2} T_{log n}` turn Dirichlet convolution into composition. The **window
representation** `ρ_A(f) H = Σ_{n ≤ e^A} f(n) n^{−1/2} T_{log n} H` is a ring homomorphism from the
arithmetic functions to the endomorphisms of `F_A` (`windowRep`):

* **Faithful modulo truncation** (`windowRep_eq_zero_iff`): `ρ_A(f) = 0` iff `f` vanishes on
  `[1, ⌊e^A⌋]`. The window algebra is the Dirichlet ring truncated at the level of the window.
* **Nesting** (`windowRepFun_of_le`): for `A ≤ B` the representations agree on `F_A ⊆ F_B`; the
  tower of window modules is a directed system over the truncations.
* **Degree derivation** (`position_comm_windowRep`): with the position `(MH)(u) = uH(u)`,
  `M ρ_A(f) − ρ_A(f) M = ρ_A(f · log)`.
* **Tate twist** (`windowRepFun_twist`): conjugation by `e^{ku}` multiplies the coefficient of `n`
  by `n^{−k}`.
* **Möbius inversion and the logarithmic derivative** (`windowRep_moebius_mul_zeta`,
  `windowRep_vonMangoldt_eq`): `ρ_A(μ)` inverts the window zeta operator `ρ_A(ζ)`, and
  `ρ_A(Λ) = (M ρ_A(ζ) − ρ_A(ζ) M) ρ_A(μ)`: the von Mangoldt operator of a window is the logarithmic
  derivative of the window zeta operator along the position.
* **Weil's window form** (`weilQuad_eq_windowRep`): on window tests,
  `Q(H) = Ω(0)‖H‖² + J_∞(H) − 2⟨ρ_A(Λ)H, H⟩ + ½⟨c,H⟩² − ½⟨s,H⟩²`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

/-! ### The window module and window shifts -/

/-- The **window module** `F_A`: real functions vanishing off `[−A, 0]`. -/
def windowSupported (A : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {H | ∀ y, y ∉ Icc (-A) 0 → H y = 0}
  add_mem' {H K} hH hK y hy := by simp [hH y hy, hK y hy]
  zero_mem' _ _ := rfl
  smul_mem' c H hH y hy := by simp [hH y hy]

theorem mem_windowSupported {A : ℝ} {H : ℝ → ℝ} :
    H ∈ windowSupported A ↔ ∀ y, y ∉ Icc (-A) 0 → H y = 0 := Iff.rfl

theorem mem_windowSupported_of_isWindowTest {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    H ∈ windowSupported A := hH.vanish

theorem windowSupported_mono {A B : ℝ} (hAB : A ≤ B) : windowSupported A ≤ windowSupported B :=
  fun _ hH y hy => hH y fun hm => hy ⟨by linarith [hm.1], hm.2⟩

/-- The **window shift** `(T_t H)(u) = 1_{u ≤ 0} H(u − t)`. -/
def windowShift (t : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := (Iic (0 : ℝ)).indicator fun u => H (u - t)

theorem windowShift_apply_of_le {t u : ℝ} (H : ℝ → ℝ) (hu : u ≤ 0) :
    windowShift t H u = H (u - t) := indicator_of_mem (mem_Iic.mpr hu) _

theorem windowShift_apply_of_pos {t u : ℝ} (H : ℝ → ℝ) (hu : 0 < u) : windowShift t H u = 0 :=
  indicator_of_notMem (fun h => by linarith [mem_Iic.mp h]) _

/-- On window functions the cut is invisible: `T_t H(u) · H(u) = H(u − t) H(u)`. -/
theorem windowShift_mul_self {A t : ℝ} {H : ℝ → ℝ} (hH : H ∈ windowSupported A) (u : ℝ) :
    windowShift t H u * H u = H (u - t) * H u := by
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le H hu]
  · rw [windowShift_apply_of_pos H hu, hH u fun hm => by linarith [hm.2], mul_zero, mul_zero]

/-- **The window shifts compose**: `T_s T_t = T_{s+t}` for `s ≥ 0`. -/
theorem windowShift_add {s : ℝ} (hs : 0 ≤ s) (t : ℝ) (H : ℝ → ℝ) :
    windowShift s (windowShift t H) = windowShift (s + t) H := by
  funext u
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu, windowShift_apply_of_le _ (by linarith),
      windowShift_apply_of_le _ hu, sub_sub]
  · rw [windowShift_apply_of_pos _ hu, windowShift_apply_of_pos _ hu]

theorem windowShift_mem {A t : ℝ} (ht : 0 ≤ t) {H : ℝ → ℝ} (hH : H ∈ windowSupported A) :
    windowShift t H ∈ windowSupported A := fun y hy => by
  rcases le_or_gt y 0 with h0 | h0
  · rw [windowShift_apply_of_le H h0]
    exact hH _ fun hm => hy ⟨by linarith [hm.1], h0⟩
  · exact windowShift_apply_of_pos H h0

theorem windowShift_zero {A : ℝ} {H : ℝ → ℝ} (hH : H ∈ windowSupported A) :
    windowShift 0 H = H := by
  funext u
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le H hu, sub_zero]
  · rw [windowShift_apply_of_pos H hu, hH u fun hm => by linarith [hm.2]]

/-- **Window shifts die past the length**: `T_t = 0` on `F_A` for `t > A`. -/
theorem windowShift_eq_zero {A t : ℝ} (ht : A < t) {H : ℝ → ℝ} (hH : H ∈ windowSupported A) :
    windowShift t H = 0 := by
  funext u
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le H hu, hH _ fun hm => by linarith [hm.1]]; rfl
  · rw [windowShift_apply_of_pos H hu]; rfl

theorem windowShift_add_fun (t : ℝ) (H K : ℝ → ℝ) :
    windowShift t (H + K) = windowShift t H + windowShift t K := by
  funext u
  rcases le_or_gt u 0 with hu | hu
  · simp only [Pi.add_apply, windowShift_apply_of_le _ hu]
  · simp only [Pi.add_apply, windowShift_apply_of_pos _ hu, add_zero]

theorem windowShift_smul (t c : ℝ) (H : ℝ → ℝ) :
    windowShift t (c • H) = c • windowShift t H := by
  funext u
  rcases le_or_gt u 0 with hu | hu
  · simp only [Pi.smul_apply, windowShift_apply_of_le _ hu]
  · simp only [Pi.smul_apply, windowShift_apply_of_pos _ hu, smul_zero]

theorem windowShift_sum {ι : Type*} (s : Finset ι) (t : ℝ) (c : ι → ℝ) (K : ι → ℝ → ℝ) (u : ℝ) :
    windowShift t (fun v => ∑ i ∈ s, c i * K i v) u = ∑ i ∈ s, c i * windowShift t (K i) u := by
  rcases le_or_gt u 0 with hu | hu
  · simp only [windowShift_apply_of_le _ hu]
  · simp only [windowShift_apply_of_pos _ hu, mul_zero, Finset.sum_const_zero]

/-! ### The window representation -/

/-- The level of an active prime power: `log n ≤ A` for `1 ≤ n ≤ ⌊e^A⌋`. -/
theorem log_le_of_mem_Icc_one {A : ℝ} {n : ℕ} (hn : n ∈ Finset.Icc 1 (windowLevel A)) :
    0 ≤ Real.log n ∧ Real.log n ≤ A := by
  obtain ⟨h1, hL⟩ := Finset.mem_Icc.mp hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
  have hnA : (n : ℝ) ≤ Real.exp A := (Nat.le_floor_iff (Real.exp_pos A).le).mp hL
  exact ⟨Real.log_nonneg hn1, (Real.log_le_iff_le_exp (by linarith)).mpr hnA⟩

/-- Beyond the level, `log n > A`. -/
theorem lt_log_of_windowLevel_lt {A : ℝ} {n : ℕ} (hn : windowLevel A < n) : A < Real.log n := by
  have hn' : Real.exp A < n := (Nat.floor_lt (Real.exp_pos A).le).mp hn
  exact (Real.lt_log_iff_exp_lt ((Real.exp_pos A).trans hn')).mpr hn'

/-- The underlying function of `ρ_A(f) H = Σ_{1 ≤ n ≤ e^A} f(n) n^{−1/2} T_{log n} H`. -/
def windowRepFun (A : ℝ) (f : ArithmeticFunction ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun u =>
  ∑ n ∈ Finset.Icc 1 (windowLevel A), f n / Real.sqrt n * windowShift (Real.log n) H u

theorem windowShift_windowRepFun (t A : ℝ) (g : ArithmeticFunction ℝ) (H : ℝ → ℝ) (u : ℝ) :
    windowShift t (windowRepFun A g H) u = ∑ n ∈ Finset.Icc 1 (windowLevel A),
      g n / Real.sqrt n * windowShift t (windowShift (Real.log n) H) u :=
  windowShift_sum _ t (fun n => g n / Real.sqrt n) (fun n => windowShift (Real.log n) H) u

theorem windowRepFun_mem {A : ℝ} (f : ArithmeticFunction ℝ) {H : ℝ → ℝ}
    (hH : H ∈ windowSupported A) : windowRepFun A f H ∈ windowSupported A := fun y hy => by
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [windowShift_mem (log_le_of_mem_Icc_one hn).1 hH y hy, mul_zero]

/-- **Nesting**: on `F_A` the representation of a longer window is that of `A`. -/
theorem windowRepFun_of_le {A B : ℝ} (hAB : A ≤ B) (f : ArithmeticFunction ℝ) {H : ℝ → ℝ}
    (hH : H ∈ windowSupported A) : windowRepFun B f H = windowRepFun A f H := by
  funext u
  refine (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (windowLevel_mono hAB))
    fun n hnB hnA => ?_).symm
  have hlt : windowLevel A < n := by
    by_contra h
    exact hnA (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnB).1, not_lt.mp h⟩)
  rw [windowShift_eq_zero (lt_log_of_windowLevel_lt hlt) hH, Pi.zero_apply, mul_zero]

theorem windowRepFun_add_fun (A : ℝ) (f : ArithmeticFunction ℝ) (H K : ℝ → ℝ) :
    windowRepFun A f (H + K) = windowRepFun A f H + windowRepFun A f K := by
  funext u
  simp only [windowRepFun, Pi.add_apply, windowShift_add_fun, mul_add, Finset.sum_add_distrib]

theorem windowRepFun_smul (A : ℝ) (f : ArithmeticFunction ℝ) (c : ℝ) (H : ℝ → ℝ) :
    windowRepFun A f (c • H) = c • windowRepFun A f H := by
  funext u
  simp only [windowRepFun, Pi.smul_apply, windowShift_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem windowRepFun_add (A : ℝ) (f g : ArithmeticFunction ℝ) (H : ℝ → ℝ) :
    windowRepFun A (f + g) H = windowRepFun A f H + windowRepFun A g H := by
  funext u
  simp only [windowRepFun, Pi.add_apply, ArithmeticFunction.add_apply, add_div, add_mul,
    Finset.sum_add_distrib]

theorem windowRepFun_zero (A : ℝ) (H : ℝ → ℝ) : windowRepFun A 0 H = 0 := by
  funext u
  simp [windowRepFun]

theorem windowRepFun_one {A : ℝ} {H : ℝ → ℝ} (hH : H ∈ windowSupported A) :
    windowRepFun A 1 H = H := by
  funext u
  by_cases hA : 1 ≤ windowLevel A
  · rw [windowRepFun, Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_rfl, hA⟩)
      fun n _ hn => by rw [ArithmeticFunction.one_apply_ne hn, zero_div, zero_mul]]
    simp only [ArithmeticFunction.one_one, Nat.cast_one, Real.sqrt_one, div_one, one_mul,
      Real.log_one, windowShift_zero hH]
  · -- `⌊e^A⌋ = 0` forces `A < 0`: the window is empty
    have hA0 : A < 0 := by
      by_contra h
      exact hA (Nat.one_le_floor_iff _ |>.mpr (Real.one_le_exp (not_lt.mp h)))
    rw [hH u fun hm => by linarith [hm.1, hm.2]]
    refine Finset.sum_eq_zero fun n hn => ?_
    exact absurd ((Finset.mem_Icc.mp hn).1.trans (Finset.mem_Icc.mp hn).2) hA

/-- The products of two active prime powers, regrouped by their product. -/
theorem sum_Icc_divisorsAntidiagonal (N : ℕ) (G : ℕ × ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 N, ∑ x ∈ k.divisorsAntidiagonal, G x =
      ∑ x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun x => x.1 * x.2 ≤ N), G x := by
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ⟨a, b⟩
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal,
      Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨k, ⟨hk1, hkN⟩, hab, hk0⟩
      have ha : 1 ≤ a := Nat.pos_of_ne_zero fun h => hk0 (by rw [← hab, h, zero_mul])
      have hb : 1 ≤ b := Nat.pos_of_ne_zero fun h => hk0 (by rw [← hab, h, mul_zero])
      refine ⟨⟨⟨ha, ?_⟩, hb, ?_⟩, by omega⟩
      · exact (Nat.le_mul_of_pos_right a hb).trans (hab ▸ hkN)
      · exact (Nat.le_mul_of_pos_left b ha).trans (hab ▸ hkN)
    · rintro ⟨⟨⟨ha, _⟩, hb, _⟩, hab⟩
      exact ⟨a * b, ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hab⟩, rfl,
        Nat.mul_ne_zero (by omega) (by omega)⟩
  · intro k _ l _ hkl
    refine Finset.disjoint_left.mpr fun x hk hl => hkl ?_
    rw [Nat.mem_divisorsAntidiagonal] at hk hl
    rw [← hk.1, ← hl.1]

/-- **Multiplicativity**: `ρ_A(f) ρ_A(g) = ρ_A(f * g)` on `F_A`. -/
theorem windowRepFun_mul {A : ℝ} (f g : ArithmeticFunction ℝ) {H : ℝ → ℝ}
    (hH : H ∈ windowSupported A) :
    windowRepFun A f (windowRepFun A g H) = windowRepFun A (f * g) H := by
  funext u
  set N := windowLevel A
  -- the composed shift `T_{log a} T_{log b} = T_{log ab}`, and `T_{log ab} = 0` beyond the level
  set G : ℕ × ℕ → ℝ := fun x => f x.1 * g x.2 / Real.sqrt (x.1 * x.2 : ℕ) *
    windowShift (Real.log (x.1 * x.2 : ℕ)) H u with hG
  have hlhs : windowRepFun A f (windowRepFun A g H) u =
      ∑ x ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, G x := by
    rw [Finset.sum_product, windowRepFun]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [windowShift_windowRepFun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
    rw [windowShift_add (log_le_of_mem_Icc_one ha).1, hG]
    simp only
    rw [Nat.cast_mul, Real.sqrt_mul (by linarith), Real.log_mul (by linarith) (by linarith)]
    field_simp
  have hrhs : windowRepFun A (f * g) H u =
      ∑ k ∈ Finset.Icc 1 N, ∑ x ∈ k.divisorsAntidiagonal, G x := by
    rw [windowRepFun]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ArithmeticFunction.mul_apply, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hG, (Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [hlhs, hrhs, sum_Icc_divisorsAntidiagonal, Finset.sum_filter_of_ne]
  intro x _ hx
  by_contra hle
  apply hx
  rw [hG]
  simp only
  rw [windowShift_eq_zero (lt_log_of_windowLevel_lt (not_le.mp hle)) hH, Pi.zero_apply, mul_zero]

/-- **The window representation** `ρ_A : (arithmetic functions) →+* End(F_A)`. -/
def windowRep (A : ℝ) : ArithmeticFunction ℝ →+* Module.End ℝ (windowSupported A) where
  toFun f :=
    { toFun := fun H => ⟨windowRepFun A f H, windowRepFun_mem f H.2⟩
      map_add' := fun H K => Subtype.ext (windowRepFun_add_fun A f H K)
      map_smul' := fun c H => Subtype.ext (windowRepFun_smul A f c H) }
  map_one' := LinearMap.ext fun H => Subtype.ext (windowRepFun_one H.2)
  map_mul' f g := LinearMap.ext fun H => Subtype.ext (windowRepFun_mul f g H.2).symm
  map_zero' := LinearMap.ext fun H => Subtype.ext (windowRepFun_zero A H)
  map_add' f g := LinearMap.ext fun H => Subtype.ext (windowRepFun_add A f g H)

theorem windowRep_apply (A : ℝ) (f : ArithmeticFunction ℝ) (H : windowSupported A) :
    (windowRep A f H : ℝ → ℝ) = windowRepFun A f H := rfl

/-! ### Faithfulness modulo truncation -/

/-- The point mass at the left end of the window. -/
def leftEndPoint (A : ℝ) : ℝ → ℝ := ({-A} : Set ℝ).indicator 1

theorem leftEndPoint_mem {A : ℝ} (hA : 0 ≤ A) : leftEndPoint A ∈ windowSupported A :=
  fun y hy => indicator_of_notMem (fun h => hy (by
    rw [mem_singleton_iff.mp h]; exact ⟨le_rfl, by linarith⟩)) _

/-- `ρ_A(f)` applied to the left end point reads the coefficient `f(m)/√m` at `log m − A`. -/
theorem windowRepFun_leftEndPoint {A : ℝ} (f : ArithmeticFunction ℝ) {m : ℕ}
    (hm : m ∈ Finset.Icc 1 (windowLevel A)) :
    windowRepFun A f (leftEndPoint A) (Real.log m - A) = f m / Real.sqrt m := by
  have hle := (log_le_of_mem_Icc_one hm).2
  rw [windowRepFun, Finset.sum_eq_single_of_mem m hm]
  · rw [windowShift_apply_of_le _ (by linarith), sub_sub_cancel_left, leftEndPoint,
      indicator_of_mem (mem_singleton _), Pi.one_apply, mul_one]
  · intro n hn hnm
    rw [windowShift_apply_of_le _ (by linarith), leftEndPoint, indicator_of_notMem, mul_zero]
    intro h
    have heq : Real.log m = Real.log n := by linarith [mem_singleton_iff.mp h]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact hnm (by exact_mod_cast Real.log_injOn_pos hn0 hm0 heq.symm)

/-- **The window algebra is the truncated Dirichlet ring**: `ρ_A(f) = 0` iff `f` vanishes on
`[1, ⌊e^A⌋]`. -/
theorem windowRep_eq_zero_iff {A : ℝ} (f : ArithmeticFunction ℝ) :
    windowRep A f = 0 ↔ ∀ n ∈ Finset.Icc 1 (windowLevel A), f n = 0 := by
  constructor
  · intro h m hm
    have hA : 0 ≤ A := by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have := (log_le_of_mem_Icc_one hm)
      linarith [this.1, this.2]
    have h0 := congrArg (fun φ : Module.End ℝ (windowSupported A) =>
      (φ ⟨leftEndPoint A, leftEndPoint_mem hA⟩ : ℝ → ℝ) (Real.log m - A)) h
    simp only [windowRep_apply, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply] at h0
    rw [windowRepFun_leftEndPoint f hm] at h0
    have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
    exact (div_eq_zero_iff.mp h0).resolve_right hs.ne'
  · intro h
    refine LinearMap.ext fun H => Subtype.ext (funext fun u => ?_)
    rw [windowRep_apply, windowRepFun]
    exact Finset.sum_eq_zero fun n hn => by rw [h n hn, zero_div, zero_mul]

/-! ### The position, the degree derivation and Tate twists -/

/-- The **position operator** `(MH)(u) = u H(u)` on `F_A`. -/
def positionOp (A : ℝ) : Module.End ℝ (windowSupported A) where
  toFun H := ⟨fun u => u * (H : ℝ → ℝ) u, fun y hy =>
    show y * (H : ℝ → ℝ) y = 0 by rw [H.2 y hy, mul_zero]⟩
  map_add' H K := Subtype.ext (funext fun u => by simp [mul_add])
  map_smul' c H := Subtype.ext (funext fun u => by simp; ring)

/-- `T_t(MH) − M T_t H = −t T_t H`. -/
theorem windowShift_position (t : ℝ) (H : ℝ → ℝ) (u : ℝ) :
    windowShift t (fun v => v * H v) u - u * windowShift t H u = -(t * windowShift t H u) := by
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu, windowShift_apply_of_le _ hu]; ring
  · rw [windowShift_apply_of_pos _ hu, windowShift_apply_of_pos _ hu]; ring

/-- **The degree derivation is the commutator with the position**:
`M ρ_A(f) − ρ_A(f) M = ρ_A(f · log)`. -/
theorem position_comm_windowRep (A : ℝ) (f : ArithmeticFunction ℝ) :
    positionOp A * windowRep A f - windowRep A f * positionOp A =
      windowRep A (f.pmul ArithmeticFunction.log) := by
  refine LinearMap.ext fun H => Subtype.ext (funext fun u => ?_)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  change u * windowRepFun A f H u - windowRepFun A f (fun v => v * (H : ℝ → ℝ) v) u =
    windowRepFun A (f.pmul ArithmeticFunction.log) H u
  simp only [windowRepFun, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have := windowShift_position (Real.log n) (H : ℝ → ℝ) u
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]
  linear_combination (-(f n / Real.sqrt n)) * this

/-- The Tate twist `n ↦ f(n) n^{−k}`. -/
def tateTwist (k : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * (n : ℝ) ^ (-k), by simp⟩

theorem tateTwist_apply (k : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    tateTwist k f n = f n * (n : ℝ) ^ (-k) := rfl

/-- **Tate twists are conjugations by exponentials**:
`ρ_A(f)(e^{k·}H)(u) = e^{ku} ρ_A(f n^{−k}) H(u)`. -/
theorem windowRepFun_twist (A k : ℝ) (f : ArithmeticFunction ℝ) (H : ℝ → ℝ) (u : ℝ) :
    windowRepFun A f (fun v => Real.exp (k * v) * H v) u =
      Real.exp (k * u) * windowRepFun A (tateTwist k f) H u := by
  simp only [windowRepFun, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [tateTwist_apply, Real.rpow_def_of_pos hn0]
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu, windowShift_apply_of_le _ hu,
      show k * (u - Real.log n) = k * u + Real.log n * -k by ring, Real.exp_add]
    ring
  · rw [windowShift_apply_of_pos _ hu, windowShift_apply_of_pos _ hu]; ring

/-! ### Möbius inversion and the logarithmic derivative -/

/-- `ρ_A(μ)` inverts the window zeta operator. -/
theorem windowRep_moebius_mul_zeta (A : ℝ) :
    windowRep A (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
      windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 := by
  rw [← map_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta, map_one]

theorem windowRep_zeta_mul_moebius (A : ℝ) :
    windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      windowRep A (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = 1 := by
  rw [← map_mul, ArithmeticFunction.coe_zeta_mul_coe_moebius, map_one]

theorem pmul_zeta_log :
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ).pmul ArithmeticFunction.log =
      ArithmeticFunction.log := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hn.ne', Nat.cast_one, one_mul]

/-- **The von Mangoldt operator is the logarithmic derivative of the window zeta operator**:
`ρ_A(Λ) ρ_A(ζ) = M ρ_A(ζ) − ρ_A(ζ) M`, hence `ρ_A(Λ) = (M ρ_A(ζ) − ρ_A(ζ) M) ρ_A(μ)`. -/
theorem windowRep_vonMangoldt_mul_zeta (A : ℝ) :
    windowRep A ArithmeticFunction.vonMangoldt *
      windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      positionOp A * windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ) -
        windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * positionOp A := by
  rw [position_comm_windowRep, pmul_zeta_log, ← map_mul,
    ArithmeticFunction.vonMangoldt_mul_zeta]

theorem windowRep_vonMangoldt_eq (A : ℝ) :
    windowRep A ArithmeticFunction.vonMangoldt =
      (positionOp A * windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ) -
        windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * positionOp A) *
        windowRep A (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  rw [← windowRep_vonMangoldt_mul_zeta, mul_assoc, windowRep_zeta_mul_moebius, mul_one]

/-! ### Weil's window form in the window algebra -/

/-- `⟨T_ℓ H, H⟩ = ∫ H(u) H(u + ℓ)` on window functions. -/
theorem integral_windowShift_mul {A ℓ : ℝ} {H : ℝ → ℝ} (hH : H ∈ windowSupported A) :
    ∫ u, windowShift ℓ H u * H u = ∫ u, H u * H (u + ℓ) := by
  simp_rw [windowShift_mul_self hH]
  rw [← integral_sub_right_eq_self (fun u => H u * H (u + ℓ)) ℓ]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [sub_add_cancel]

/-- The arithmetic pairing `⟨ρ_A(Λ)H, H⟩ = Σ_{2 ≤ n ≤ e^A} (Λ(n)/√n) ∫ H(u) H(u + log n)`. -/
theorem integral_windowRep_vonMangoldt_mul {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u =
      ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * ∫ u, H u * H (u + Real.log n) := by
  have hmem := mem_windowSupported_of_isWindowTest hH
  have hint : ∀ n ∈ Finset.Icc 1 (windowLevel A), Integrable fun u =>
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (windowShift (Real.log n) H u * H u) := fun n _ => by
    refine Integrable.const_mul ?_ _
    simp_rw [windowShift_mul_self hmem]
    have := integrable_mul_shift hH.continuous hH.hasCompactSupport (-Real.log n)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [sub_eq_add_neg]
    ring
  simp_rw [windowRepFun, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ hint]
  have hsplit : Finset.Icc 1 (windowLevel A) =
      insert 1 (Finset.Icc 2 (windowLevel A)) ∨ windowLevel A = 0 := by
    rcases Nat.eq_zero_or_pos (windowLevel A) with h | h
    · exact Or.inr h
    · left
      ext n
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
  rcases hsplit with hs | h0
  · rw [hs, Finset.sum_insert (by simp)]
    simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul, integral_zero,
      zero_add]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, integral_windowShift_mul hmem, primeJumpWeight]
  · rw [h0]; simp

/-- **Weil's window form in the window algebra**:
`Q(H) = Ω(0)‖H‖² + J_∞(H) − 2⟨ρ_A(Λ)H, H⟩ + ½⟨c,H⟩² − ½⟨s,H⟩²`. -/
theorem weilQuad_eq_windowRep {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    weilQuad H = EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H -
      2 * (∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u) +
        (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) := by
  have hc := hH.continuous
  have hcs := hH.hasCompactSupport
  have hjump : ∀ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n *
      (∫ u, (H u - H (u + Real.log n)) ^ 2) = primeJumpWeight n *
        (2 * (∫ u, H u ^ 2) - 2 * ∫ u, H u * H (u + Real.log n)) := fun n _ => by
    congr 1
    have iH := integrable_sq hc hcs
    have iHs : Integrable fun u => H (u + Real.log n) ^ 2 :=
      integrable_sq (hc.comp (continuous_add_const _)) (hasCompactSupport_comp_add hcs _)
    have iP := integrable_mul_shift hc hcs (Real.log n)
    have hexp : ∀ u, (H u - H (u + Real.log n)) ^ 2 =
        H u ^ 2 + H (u + Real.log n) ^ 2 - 2 * (H u * H (u + Real.log n)) := fun u => by ring
    simp_rw [hexp]
    rw [integral_add_sub_two_mul iH iHs iP,
      integral_add_right_eq_self (fun u => H u ^ 2) (Real.log n)]
    ring
  have hsum : ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n *
      (2 * (∫ u, H u ^ 2) - 2 * ∫ u, H u * H (u + Real.log n)) =
      2 * (∫ u, H u ^ 2) * (∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n) -
        2 * ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n *
          ∫ u, H u * H (u + Real.log n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [weilQuad_eq_markovForm_windowLevel hH, markovForm, creationPotential, primeJump,
    Finset.sum_congr rfl hjump, hsum, integral_windowRep_vonMangoldt_mul hH]
  ring

end GaloisForLFunctions.WindowTowerOfSpecZ
