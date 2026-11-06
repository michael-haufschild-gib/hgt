import GaloisForLFunctions.RHTower.ZetaGateUpperHighBlock
import GaloisForLFunctions.RHTower.ZetaGateProductAFESharpHighBlock
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments

/-!
# The twisted second moment factors over prime blocks

The second moment of `ζ` against a mollifier of length `≤ U^{21/50}` has main term the gcd form
`G_s(a) = Σ_{h,k} a_h a_k gcd(h,k)^s/(hk)`, `s = 1 + 2d`. This module shows that the form sees a product
of Euler pieces block by block, and turns that into a moment bound.

* **Factorization** (`gcdForm_blockConv`). If `a` and `b` are supported on coprime integers, then
  `G_s(a ⋆ b) = G_s(a) G_s(b)`: disjoint prime blocks do not interact.
* **The local factor** (`gcdForm_eulerStep`). `G_s(δ₁ − δ_p) = 1 − 2/p + p^{s−2}`, and
  `G_s(Π_{p ∈ B} (1 − p^{−z})) = Π_{p ∈ B} (1 − 2/p + p^{s−2})` (`gcdForm_eulerCoeff`).
* **The moment bound** (`exists_twisted_second_moment_le`, `exists_euler_piece_second_moment_le`). On the
  Levinson line `½ − d`, `d ≍ R/log U`, on the upper blocks of `[U^{49/50}, U]`,
  `∫_a^v |ζ Π_{p ∈ B}(1 − p^{−z})|² ≤ F(U) ((1+ε)(v−a) + ε a)`, with
  `F(U) ≈ (e^{2R}/(2R)) log U Π_{p ∈ B} (1 − 2/p + e^R/p)` as long as `Π_{p ∈ B} p ≤ U^{21/50}`.

The product `Π_{p ≤ y}(1 − 1/p) ≈ e^{−γ}/log y` is what mollification buys: each block removes its
reciprocal mass from `log U`. The length restriction is the only place where the last scale enters.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-! ### The gcd form and its factorization -/

/-- The gcd form `G_s(a) = Σ_{h,k ≤ N} a_h a_k gcd(h,k)^s/(hk)`. -/
def gcdForm (s : ℝ) (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    a h * a k * ((Nat.gcd h k : ℝ) ^ s / ((h : ℝ) * k))

theorem gcdSum₂_eq_gcdForm (d : ℝ) (N : ℕ) (a : ℕ → ℝ) :
    gcdSum₂ d N a = gcdForm (1 + 2 * d) N a := by
  rw [gcdSum₂_eq_gcd_form, Finset.sum_product]
  unfold gcdForm
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The Dirichlet convolution of two coefficient sequences of lengths `Na`, `Nb`. -/
def blockConv (a b : ℕ → ℝ) (Na Nb n : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 Na, ∑ k ∈ Finset.Icc 1 Nb, if h * k = n then a h * b k else 0

theorem mem_Icc_mul {h k Na Nb : ℕ} (hh : h ∈ Finset.Icc 1 Na) (hk : k ∈ Finset.Icc 1 Nb) :
    h * k ∈ Finset.Icc 1 (Na * Nb) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hh
  obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hk
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos h1 h3, Nat.mul_le_mul h2 h4⟩

/-- Summing a function against the convolution unfolds it into the two factors. -/
theorem sum_blockConv_mul {E : Type*} [Semiring E] [Algebra ℝ E] (a b : ℕ → ℝ) (Na Nb : ℕ) (g : ℕ → E) :
    ∑ n ∈ Finset.Icc 1 (Na * Nb), algebraMap ℝ E (blockConv a b Na Nb n) * g n =
      ∑ h ∈ Finset.Icc 1 Na, ∑ k ∈ Finset.Icc 1 Nb, algebraMap ℝ E (a h * b k) * g (h * k) := by
  classical
  unfold blockConv
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single (h * k)]
  · simp
  · intro n _ hne
    rw [if_neg (Ne.symm hne)]
    simp
  · intro hnot
    exact absurd (mem_Icc_mul hh hk) hnot

/-- Coprime parts: the gcd of two products is the product of the gcds. -/
theorem gcd_mul_mul_of_coprime {h k h' k' : ℕ} (hc : Nat.Coprime (h * h') (k * k')) :
    Nat.gcd (h * k) (h' * k') = Nat.gcd h h' * Nat.gcd k k' := by
  have hh'k' : Nat.Coprime h' k' :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left k' k) (Nat.Coprime.coprime_dvd_left (dvd_mul_left h' h) hc)
  have hkh' : Nat.Coprime k h' :=
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right k k') (Nat.Coprime.coprime_dvd_left (dvd_mul_left h' h) hc)).symm
  have hhk' : Nat.Coprime h k' :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left k' k) (Nat.Coprime.coprime_dvd_left (dvd_mul_right h h') hc)
  rw [Nat.Coprime.gcd_mul (h * k) hh'k', Nat.Coprime.gcd_mul_right_cancel h hkh',
    Nat.Coprime.gcd_mul_left_cancel k hhk']

/-- **The gcd form factors over coprime blocks.** -/
theorem gcdForm_blockConv {a b : ℕ → ℝ} {Na Nb : ℕ} (s : ℝ)
    (hcop : ∀ h ∈ Finset.Icc 1 Na, ∀ h' ∈ Finset.Icc 1 Na, ∀ k ∈ Finset.Icc 1 Nb,
      ∀ k' ∈ Finset.Icc 1 Nb, a h ≠ 0 → a h' ≠ 0 → b k ≠ 0 → b k' ≠ 0 →
        Nat.Coprime (h * h') (k * k')) :
    gcdForm s (Na * Nb) (blockConv a b Na Nb) = gcdForm s Na a * gcdForm s Nb b := by
  unfold gcdForm
  -- unfold the convolution in both variables
  have hinner : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 (Na * Nb), blockConv a b Na Nb m *
      ((Nat.gcd n m : ℝ) ^ s / ((n : ℝ) * m)) =
      ∑ h' ∈ Finset.Icc 1 Na, ∑ k' ∈ Finset.Icc 1 Nb, a h' * b k' *
        ((Nat.gcd n (h' * k') : ℝ) ^ s / ((n : ℝ) * ((h' * k' : ℕ) : ℝ))) := by
    intro n
    exact sum_blockConv_mul (E := ℝ) a b Na Nb
      (fun m => (Nat.gcd n m : ℝ) ^ s / ((n : ℝ) * m))
  have houter : ∑ n ∈ Finset.Icc 1 (Na * Nb), ∑ m ∈ Finset.Icc 1 (Na * Nb),
      blockConv a b Na Nb n * blockConv a b Na Nb m * ((Nat.gcd n m : ℝ) ^ s / ((n : ℝ) * m)) =
      ∑ h ∈ Finset.Icc 1 Na, ∑ k ∈ Finset.Icc 1 Nb, a h * b k *
        ∑ h' ∈ Finset.Icc 1 Na, ∑ k' ∈ Finset.Icc 1 Nb, a h' * b k' *
          ((Nat.gcd (h * k) (h' * k') : ℝ) ^ s /
            (((h * k : ℕ) : ℝ) * ((h' * k' : ℕ) : ℝ))) := by
    have h1 : ∀ n, ∑ m ∈ Finset.Icc 1 (Na * Nb),
        blockConv a b Na Nb n * blockConv a b Na Nb m * ((Nat.gcd n m : ℝ) ^ s / ((n : ℝ) * m)) =
        blockConv a b Na Nb n * ∑ h' ∈ Finset.Icc 1 Na, ∑ k' ∈ Finset.Icc 1 Nb, a h' * b k' *
          ((Nat.gcd n (h' * k') : ℝ) ^ s / ((n : ℝ) * ((h' * k' : ℕ) : ℝ))) := by
      intro n
      rw [← hinner, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp_rw [h1]
    exact sum_blockConv_mul (E := ℝ) a b Na Nb (fun n =>
      ∑ h' ∈ Finset.Icc 1 Na, ∑ k' ∈ Finset.Icc 1 Nb, a h' * b k' *
        ((Nat.gcd n (h' * k') : ℝ) ^ s / ((n : ℝ) * ((h' * k' : ℕ) : ℝ))))
  have hterm : ∀ h ∈ Finset.Icc 1 Na, ∀ h' ∈ Finset.Icc 1 Na, ∀ k ∈ Finset.Icc 1 Nb,
      ∀ k' ∈ Finset.Icc 1 Nb, a h * b k * (a h' * b k' *
        ((Nat.gcd (h * k) (h' * k') : ℝ) ^ s / (((h * k : ℕ) : ℝ) * ((h' * k' : ℕ) : ℝ)))) =
        (a h * a h' * ((Nat.gcd h h' : ℝ) ^ s / ((h : ℝ) * h'))) *
          (b k * b k' * ((Nat.gcd k k' : ℝ) ^ s / ((k : ℝ) * k'))) := by
    intro h hh h' hh' k hk k' hk'
    by_cases h1 : a h = 0
    · simp [h1]
    by_cases h2 : a h' = 0
    · simp [h2]
    by_cases h3 : b k = 0
    · simp [h3]
    by_cases h4 : b k' = 0
    · simp [h4]
    rw [gcd_mul_mul_of_coprime (hcop h hh h' hh' k hk k' hk' h1 h2 h3 h4)]
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  rw [houter]
  calc _ = ∑ h ∈ Finset.Icc 1 Na, ∑ h' ∈ Finset.Icc 1 Na, ∑ k ∈ Finset.Icc 1 Nb,
        ∑ k' ∈ Finset.Icc 1 Nb, (a h * a h' * ((Nat.gcd h h' : ℝ) ^ s / ((h : ℝ) * h'))) *
          (b k * b k' * ((Nat.gcd k k' : ℝ) ^ s / ((k : ℝ) * k'))) := by
        refine Finset.sum_congr rfl fun h hh => ?_
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun h' hh' => Finset.sum_congr rfl fun k hk =>
          Finset.sum_congr rfl fun k' hk' => hterm h hh h' hh' k hk k' hk'
    _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun h' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]

/-- **The coefficients of a product over coprime blocks stay bounded by one.** -/
theorem abs_blockConv_le_one {a b : ℕ → ℝ} {Na Nb : ℕ}
    (ha : ∀ h, |a h| ≤ 1) (hb : ∀ k, |b k| ≤ 1)
    (hcop : ∀ h ∈ Finset.Icc 1 Na, ∀ h' ∈ Finset.Icc 1 Na, ∀ k ∈ Finset.Icc 1 Nb,
      ∀ k' ∈ Finset.Icc 1 Nb, a h ≠ 0 → a h' ≠ 0 → b k ≠ 0 → b k' ≠ 0 →
        Nat.Coprime (h * h') (k * k')) (n : ℕ) :
    |blockConv a b Na Nb n| ≤ 1 := by
  classical
  unfold blockConv
  by_cases hex : ∃ h ∈ Finset.Icc 1 Na, ∃ k ∈ Finset.Icc 1 Nb, h * k = n ∧ a h ≠ 0 ∧ b k ≠ 0
  · obtain ⟨h₀, hh₀, k₀, hk₀, hn, ha₀, hb₀⟩ := hex
    have hprod : |a h₀ * b k₀| ≤ 1 := by
      rw [abs_mul]
      exact mul_le_one₀ (ha h₀) (abs_nonneg _) (hb k₀)
    -- any other nonzero term is the same pair
    have huniq : ∀ h ∈ Finset.Icc 1 Na, ∀ k ∈ Finset.Icc 1 Nb, h * k = n → a h ≠ 0 → b k ≠ 0 →
        h = h₀ ∧ k = k₀ := by
      intro h hh k hk hn' h1 h2
      have hc := hcop h hh h₀ hh₀ k hk k₀ hk₀ h1 ha₀ h2 hb₀
      have heq : h * k = h₀ * k₀ := by rw [hn', hn]
      have hk' : Nat.Coprime h k₀ :=
        Nat.Coprime.coprime_dvd_right (dvd_mul_left k₀ k)
          (Nat.Coprime.coprime_dvd_left (dvd_mul_right h h₀) hc)
      have hk'' : Nat.Coprime h₀ k :=
        Nat.Coprime.coprime_dvd_right (dvd_mul_right k k₀)
          (Nat.Coprime.coprime_dvd_left (dvd_mul_left h₀ h) hc)
      have d1 : h ∣ h₀ := hk'.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right h k)
      have d2 : h₀ ∣ h := hk''.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right h₀ k₀)
      have e1 : h = h₀ := Nat.dvd_antisymm d1 d2
      subst e1
      refine ⟨rfl, Nat.eq_of_mul_eq_mul_left ?_ heq⟩
      exact (Finset.mem_Icc.mp hh).1
    rw [Finset.sum_eq_single h₀, Finset.sum_eq_single k₀, if_pos hn]
    · exact hprod
    · intro k hk hne
      by_cases hcond : h₀ * k = n
      · rw [if_pos hcond]
        by_cases hbk : b k = 0
        · simp [hbk]
        · exact absurd (huniq h₀ hh₀ k hk hcond ha₀ hbk).2 hne
      · rw [if_neg hcond]
    · intro hnot
      exact absurd hk₀ hnot
    · intro h hh hne
      refine Finset.sum_eq_zero fun k hk => ?_
      by_cases hcond : h * k = n
      · rw [if_pos hcond]
        by_cases hah : a h = 0
        · simp [hah]
        by_cases hbk : b k = 0
        · simp [hbk]
        exact absurd (huniq h hh k hk hcond hah hbk).1 hne
      · rw [if_neg hcond]
    · intro hnot
      exact absurd hh₀ hnot
  · push Not at hex
    have hzero : ∑ h ∈ Finset.Icc 1 Na, ∑ k ∈ Finset.Icc 1 Nb,
        (if h * k = n then a h * b k else 0) = 0 := by
      refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun k hk => ?_
      by_cases hcond : h * k = n
      · rw [if_pos hcond]
        by_cases hah : a h = 0
        · simp [hah]
        rw [hex h hh k hk hcond hah, mul_zero]
      · rw [if_neg hcond]
    rw [hzero, abs_zero]
    exact zero_le_one

/-! ### One Euler factor -/

/-- The coefficients of `1 − p^{−z}`. -/
def eulerStep (p n : ℕ) : ℝ := if n = 1 then 1 else if n = p then -1 else 0

theorem abs_eulerStep_le (p n : ℕ) : |eulerStep p n| ≤ 1 := by
  unfold eulerStep
  split_ifs <;> simp

theorem eulerStep_ne_zero {p n : ℕ} (h : eulerStep p n ≠ 0) : n = 1 ∨ n = p := by
  unfold eulerStep at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd rfl h

theorem sum_Icc_eulerStep {E : Type*} [AddCommMonoid E] {p : ℕ} (hp : p.Prime) (F : ℕ → E)
    (hF : ∀ n, eulerStep p n = 0 → F n = 0) :
    ∑ n ∈ Finset.Icc 1 p, F n = F 1 + F p := by
  have hsub : ({1, p} : Finset ℕ) ⊆ Finset.Icc 1 p := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Finset.mem_Icc.mpr ⟨le_rfl, hp.one_lt.le⟩
    · rw [Finset.mem_singleton.mp hn]
      exact Finset.mem_Icc.mpr ⟨hp.one_lt.le, le_rfl⟩
  rw [← Finset.sum_subset hsub, Finset.sum_pair hp.one_lt.ne]
  intro n _ hn
  refine hF n ?_
  by_contra hne
  rcases eulerStep_ne_zero hne with rfl | rfl
  · exact hn (Finset.mem_insert_self _ _)
  · exact hn (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem eulerStep_one {p : ℕ} : eulerStep p 1 = 1 := by simp [eulerStep]

theorem eulerStep_self {p : ℕ} (hp : p.Prime) : eulerStep p p = -1 := by
  simp [eulerStep, hp.one_lt.ne']

/-- **The local factor of the gcd form.** `G_s(δ₁ − δ_p) = 1 − 2/p + p^{s−2}`. -/
theorem gcdForm_eulerStep {p : ℕ} (hp : p.Prime) (s : ℝ) :
    gcdForm s p (eulerStep p) = 1 - 2 / p + (p : ℝ) ^ (s - 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold gcdForm
  rw [sum_Icc_eulerStep hp _ (fun n hn => by simp [hn])]
  rw [sum_Icc_eulerStep hp _ (fun n hn => by simp [hn]),
    sum_Icc_eulerStep hp _ (fun n hn => by simp [hn])]
  rw [eulerStep_one, eulerStep_self hp]
  have hrp : (p : ℝ) ^ (s - 2) = (p : ℝ) ^ s / ((p : ℝ) * p) := by
    rw [Real.rpow_sub hp0, Real.rpow_two]
    ring_nf
  simp only [Nat.gcd_one_left, Nat.gcd_one_right, Nat.gcd_self, Nat.cast_one, Real.one_rpow]
  rw [hrp]
  field_simp
  ring

/-! ### Products of Euler factors -/

/-- The coefficients of `Π_{p ∈ B} (1 − p^{−z})`. -/
def eulerCoeff : List ℕ → ℕ → ℝ
  | [] => fun n => if n = 1 then 1 else 0
  | p :: B => blockConv (eulerStep p) (eulerCoeff B) p B.prod

theorem eulerCoeff_ne_zero_dvd (B : List ℕ) {n : ℕ} (h : eulerCoeff B n ≠ 0) : n ∣ B.prod := by
  classical
  induction B generalizing n with
  | nil =>
    simp only [eulerCoeff, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
    simp [h]
  | cons p B ih =>
    simp only [eulerCoeff, blockConv] at h
    obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨k, _, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    by_cases hcond : u * k = n
    · rw [if_pos hcond] at hne2
      have h1 : eulerStep p u ≠ 0 := left_ne_zero_of_mul hne2
      have h2 : eulerCoeff B k ≠ 0 := right_ne_zero_of_mul hne2
      rw [List.prod_cons, ← hcond]
      refine mul_dvd_mul ?_ (ih h2)
      rcases eulerStep_ne_zero h1 with rfl | rfl
      · exact one_dvd _
      · exact dvd_rfl
    · rw [if_neg hcond] at hne2
      exact absurd rfl hne2

theorem coprime_list_prod {p : ℕ} {B : List ℕ} (hp : p.Prime) (hB : ∀ q ∈ B, q.Prime) (hnot : p ∉ B) :
    Nat.Coprime p B.prod := by
  induction B with
  | nil => simp
  | cons q B ih =>
    rw [List.prod_cons]
    refine Nat.Coprime.mul_right ?_ (ih (fun r hr => hB r (List.mem_cons_of_mem q hr))
      (fun h => hnot (List.mem_cons_of_mem q h)))
    exact (Nat.coprime_primes hp (hB q List.mem_cons_self)).mpr
      (fun h => hnot (h ▸ List.mem_cons_self))

/-- The block condition for one more Euler factor. -/
theorem euler_block_coprime {p : ℕ} {B : List ℕ} (hp : Nat.Coprime p B.prod) {h h' k k' : ℕ}
    (h1 : eulerStep p h ≠ 0) (h2 : eulerStep p h' ≠ 0) (h3 : eulerCoeff B k ≠ 0)
    (h4 : eulerCoeff B k' ≠ 0) : Nat.Coprime (h * h') (k * k') := by
  have hd : ∀ {u : ℕ}, eulerStep p u ≠ 0 → u ∣ p := by
    intro u hu
    rcases eulerStep_ne_zero hu with rfl | rfl
    · exact one_dvd _
    · exact dvd_rfl
  have hk := eulerCoeff_ne_zero_dvd B h3
  have hk' := eulerCoeff_ne_zero_dvd B h4
  refine Nat.Coprime.mul_left ?_ ?_ <;> refine Nat.Coprime.mul_right ?_ ?_
  · exact Nat.Coprime.coprime_dvd_right hk (Nat.Coprime.coprime_dvd_left (hd h1) hp)
  · exact Nat.Coprime.coprime_dvd_right hk' (Nat.Coprime.coprime_dvd_left (hd h1) hp)
  · exact Nat.Coprime.coprime_dvd_right hk (Nat.Coprime.coprime_dvd_left (hd h2) hp)
  · exact Nat.Coprime.coprime_dvd_right hk' (Nat.Coprime.coprime_dvd_left (hd h2) hp)

theorem abs_eulerCoeff_le {B : List ℕ} (hB : ∀ q ∈ B, q.Prime) (hd : B.Nodup) (n : ℕ) :
    |eulerCoeff B n| ≤ 1 := by
  induction B generalizing n with
  | nil =>
    simp only [eulerCoeff]
    split_ifs <;> simp
  | cons p B ih =>
    obtain ⟨hnot, hd'⟩ := List.nodup_cons.mp hd
    have hB' : ∀ q ∈ B, q.Prime := fun q hq => hB q (List.mem_cons_of_mem p hq)
    have hc := coprime_list_prod (hB p List.mem_cons_self) hB' hnot
    exact abs_blockConv_le_one (abs_eulerStep_le p) (ih hB' hd') (fun h _ h' _ k _ k' _ h1 h2 h3 h4 =>
      euler_block_coprime hc h1 h2 h3 h4) n

/-- **The gcd form of an Euler product.** -/
theorem gcdForm_eulerCoeff {B : List ℕ} (hB : ∀ q ∈ B, q.Prime) (hd : B.Nodup) (s : ℝ) :
    gcdForm s B.prod (eulerCoeff B) =
      (B.map fun p : ℕ => 1 - 2 / (p : ℝ) + (p : ℝ) ^ (s - 2)).prod := by
  induction B with
  | nil =>
    simp [gcdForm, eulerCoeff]
  | cons p B ih =>
    obtain ⟨hnot, hd'⟩ := List.nodup_cons.mp hd
    have hB' : ∀ q ∈ B, q.Prime := fun q hq => hB q (List.mem_cons_of_mem p hq)
    have hp := hB p List.mem_cons_self
    have hc := coprime_list_prod hp hB' hnot
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    show gcdForm s (p * B.prod) (blockConv (eulerStep p) (eulerCoeff B) p B.prod) = _
    rw [gcdForm_blockConv s (fun h _ h' _ k _ k' _ h1 h2 h3 h4 =>
      euler_block_coprime hc h1 h2 h3 h4), gcdForm_eulerStep hp, ih hB' hd']

/-- **The Euler product as a Dirichlet polynomial.** -/
theorem edPoly_eulerCoeff {B : List ℕ} (hB : ∀ q ∈ B, q.Prime) (z : ℂ) :
    edPoly (fun n => ((eulerCoeff B n : ℝ) : ℂ)) (Finset.Icc 1 B.prod) z =
      (B.map fun p : ℕ => 1 - ((p : ℝ) : ℂ) ^ (-z)).prod := by
  induction B with
  | nil =>
    simp [edPoly, eulerCoeff]
  | cons p B ih =>
    have hB' : ∀ q ∈ B, q.Prime := fun q hq => hB q (List.mem_cons_of_mem p hq)
    have hp := hB p List.mem_cons_self
    simp only [List.map_cons, List.prod_cons]
    rw [← ih hB']
    unfold edPoly
    show ∑ n ∈ Finset.Icc 1 (p * B.prod),
      ((blockConv (eulerStep p) (eulerCoeff B) p B.prod n : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-z) = _
    have h := sum_blockConv_mul (E := ℂ) (eulerStep p) (eulerCoeff B) p B.prod
      (fun n => ((n : ℝ) : ℂ) ^ (-z))
    simp only [Complex.coe_algebraMap] at h
    rw [h]
    have hstep : ((1 : ℂ) - ((p : ℝ) : ℂ) ^ (-z)) =
        ∑ h ∈ Finset.Icc 1 p, ((eulerStep p h : ℝ) : ℂ) * ((h : ℝ) : ℂ) ^ (-z) := by
      rw [sum_Icc_eulerStep hp _ (fun n hn => by simp [hn]), eulerStep_one, eulerStep_self hp]
      simp
      ring
    rw [hstep, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ofReal_natCast_mul_cpow_neg]
    push_cast
    ring

/-! ### The moment bound -/

/-- Scaling a real mollifier scales the quadratic main term. -/
theorem gcdSum₂_div_sqrt (d : ℝ) (N : ℕ) (w : ℕ → ℝ) {F : ℝ} (hF : 0 < F) :
    gcdSum₂ d N (fun n => w n / Real.sqrt F) = gcdSum₂ d N w / F := by
  unfold gcdSum₂
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : Real.sqrt F * Real.sqrt F = F := Real.mul_self_sqrt hF.le
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ((h : ℝ) * k) ^ (-(1 / 2 - d)) *
    ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d)) := ⟨_, rfl⟩
  rw [← hX]
  calc w h / Real.sqrt F * (w k / Real.sqrt F) * X
      = w h * w k * X / (Real.sqrt F * Real.sqrt F) := by ring
    _ = _ := by rw [hs]

/-- **The twisted second moment on the upper blocks.** Every bounded real mollifier of length
`≤ U^{21/50}` with main term `≤ (v − a + 2η) F(U)` has
`∫_a^v |ζΨ(½ − d + iτ)|² dτ ≤ F(U) ((1+ε)(v−a) + ε a)`. The bound `F` may tend to infinity. -/
theorem exists_twisted_second_moment_le {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (N : ℝ → ℕ)
    (w : ℝ → ℕ → ℝ) (hN : ∀ᶠ U in atTop, (N U : ℝ) ≤ U ^ ((21 : ℝ) / 50))
    (hw : ∀ U, ∀ n ∈ Finset.Icc 1 (N U), |w U n| ≤ 1) (hF1 : ∀ᶠ U in atTop, 1 ≤ F U)
    (hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (N U) (w U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * F U) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((49 : ℝ) / 50) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ F U * ((1 + ε) * (v - a) + ε * a) := by
  intro ε hε
  obtain ⟨F', hF'⟩ : ∃ F' : ℝ → ℝ, F' = fun U => max 1 (F U) := ⟨_, rfl⟩
  have hF'1 : ∀ U, 1 ≤ F' U := fun U => by
    rw [hF']
    exact le_max_left _ _
  have hF'0 : ∀ U, 0 < F' U := fun U => by linarith [hF'1 U]
  have hscale := exists_highBlock_bound_of_mainTerm_upper hR
    (F := fun _ => 1) (c := 1) tendsto_const_nhds N (fun U n => w U n / Real.sqrt (F' U)) hN
    (fun U n hn => by
      rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr (hF'0 U))]
      refine (div_le_one (Real.sqrt_pos.mpr (hF'0 U))).mpr ((hw U n hn).trans ?_)
      exact Real.one_le_sqrt.mpr (hF'1 U))
    (by
      filter_upwards [hmain, hF1] with U hU hFU d hd hd8 hRd hdU a v η hη h4 hav hvU hηa haη haU
      have hFeq : F' U = F U := by
        rw [hF']
        exact max_eq_right hFU
      rw [gcdSum₂_div_sqrt d (N U) (w U) (hF'0 U), hFeq, mul_one]
      have h := hU d hd hd8 hRd hdU a v η hη h4 hav hvU hηa haη haU
      have hFpos : 0 < F U := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hFpos]
      exact h)
    ε hε
  filter_upwards [hscale, hF1] with U hU hFU d hd hd8 hRd hdU a v ha haU hav hv2 hvU
  have hFeq : F' U = F U := by
    rw [hF']
    exact max_eq_right hFU
  have hFpos : 0 < F U := by linarith
  have hb := hU d hd hd8 hRd hdU a v ha haU hav hv2 hvU
  rw [hFeq] at hb
  have hs : Real.sqrt (F U) * Real.sqrt (F U) = F U := Real.mul_self_sqrt hFpos.le
  have hs0 : 0 < Real.sqrt (F U) := Real.sqrt_pos.mpr hFpos
  have hpt : ∀ τ : ℝ, ‖riemannZeta (displacedLinePt d τ) *
      edPoly (fun n => ((w U n / Real.sqrt (F U) : ℝ) : ℂ)) (Finset.Icc 1 (N U))
        (displacedLinePt d τ)‖ ^ 2 =
      (F U)⁻¹ * ‖riemannZeta (displacedLinePt d τ) *
        edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2 := by
    intro τ
    have hscaleE : edPoly (fun n => ((w U n / Real.sqrt (F U) : ℝ) : ℂ)) (Finset.Icc 1 (N U))
        (displacedLinePt d τ) = (((Real.sqrt (F U))⁻¹ : ℝ) : ℂ) *
        edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ) := by
      unfold edPoly
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      rw [div_eq_mul_inv]
      ring
    rw [hscaleE, mul_left_comm, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      inv_pow, sq, hs]
  simp_rw [hpt] at hb
  rw [intervalIntegral.integral_const_mul, inv_mul_le_iff₀ hFpos] at hb
  exact hb

/-- The main term of the second moment, from a bound on the gcd form. -/
theorem mainTerm_le_of_gcdSum_le {R U d a v η G : ℝ} {N : ℕ} {w : ℕ → ℝ} (hR : 0 < R) (hd : 0 < d)
    (hd8 : d ≤ 1 / 8) (hRd : R ≤ d * Real.log U) (hdU1 : d * Real.log (U - 1) ≤ R) (hU3 : 3 ≤ U)
    (hη : 0 < η) (h4 : 4 ≤ a - η) (hav : a ≤ v) (hvU : v ≤ U) (hηa : η ≤ a) (haη : a / 2 ≤ a - η)
    (haU : U ^ ((1 : ℝ) / 8) ≤ a) (hG0 : 0 ≤ G) (hS : gcdSum₂ d N w ≤ G) :
    gcdSum₂ d N w * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ (v - a + 2 * η) * (G * ((3 / 2 + Real.log U / (2 * R)) *
          (Real.exp (2 * R * (Real.log U / Real.log (U - 1))) *
            Real.exp (5 * U ^ (-(1 / 8 : ℝ)))))) := by
  have hU0 : 0 < U := by linarith only [hU3]
  have hlogU0 : 0 < Real.log U := Real.log_pos (by linarith only [hU3])
  have hlogU1 : 0 < Real.log (U - 1) := Real.log_pos (by linarith only [hU3])
  have hd4 : d ≤ 1 / 4 := by linarith only [hd8]
  have hlen : 0 ≤ v - a + 2 * η := by linarith only [hav, hη]
  have hζ := norm_riemannZeta_one_add_le (by linarith only [hd] : 0 < 2 * d)
  have hχ := norm_integral_window_chiPairWeight_le_sharp hd hd4 hη h4 hav
  have h1d := inv_two_mul_le hd hR hRd
  have hF4 := chiWindowWeight_le hd.le hU0 hlogU0.le hlogU1 hdU1
    (y := v + η) (by linarith only [hav, h4, hη]) (by linarith only [hvU, hηa, hav])
  have hF5 := exp_chiWindowError_le hd8 haη h4 hU0 haU
  have hZ : ‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖ ≤ 3 / 2 + Real.log U / (2 * R) :=
    hζ.trans (by linarith only [h1d])
  have hX : ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖
      ≤ (v - a + 2 * η) * (Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
          * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))) := by
    refine hχ.trans (mul_le_mul_of_nonneg_left ?_ hlen)
    exact mul_le_mul hF4 hF5 (Real.exp_pos _).le (Real.exp_pos _).le
  have hZ0 : 0 ≤ 3 / 2 + Real.log U / (2 * R) := by positivity
  calc gcdSum₂ d N w * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ G * ((3 / 2 + Real.log U / (2 * R)) * ((v - a + 2 * η) *
          (Real.exp (2 * R * (Real.log U / Real.log (U - 1))) *
            Real.exp (5 * U ^ (-(1 / 8 : ℝ)))))) :=
        mul_le_mul hS (mul_le_mul hZ hX (norm_nonneg _) hZ0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hG0
    _ = _ := by ring

/-- The local factor of the Euler main term at height `U`, uniform in the admissible displacement. -/
def eulerLocal (R U : ℝ) (p : ℕ) : ℝ :=
  1 - 2 / (p : ℝ) + Real.exp (2 * R * (Real.log p / Real.log (U - 1))) / p

/-- The main term `F₀(U) ≈ (e^{2R}/(2R)) log U Π_{p ∈ B} (1 − 2/p + p^{2R/log U}/p)`. -/
def eulerMain (R U : ℝ) (B : List ℕ) : ℝ :=
  (B.map (eulerLocal R U)).prod * ((3 / 2 + Real.log U / (2 * R)) *
    (Real.exp (2 * R * (Real.log U / Real.log (U - 1))) * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))))

theorem eulerLocal_nonneg {R U : ℝ} {p : ℕ} (hp : p.Prime) : 0 ≤ eulerLocal R U p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hp2
  unfold eulerLocal
  have : 0 ≤ Real.exp (2 * R * (Real.log p / Real.log (U - 1))) / p := by positivity
  linarith

/-- A product of local factors at the admissible displacement is dominated by the uniform one. -/
theorem prod_local_le {R U d : ℝ} {B : List ℕ} (hB : ∀ q ∈ B, q.Prime) (hU3 : 3 ≤ U)
    (hdU1 : d * Real.log (U - 1) ≤ R) :
    (B.map fun p : ℕ => 1 - 2 / (p : ℝ) + (p : ℝ) ^ (1 + 2 * d - 2)).prod ≤
      (B.map (eulerLocal R U)).prod := by
  induction B with
  | nil => simp
  | cons p B ih =>
    have hB' : ∀ q ∈ B, q.Prime := fun q hq => hB q (List.mem_cons_of_mem p hq)
    have hp := hB p List.mem_cons_self
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogU : 0 < Real.log (U - 1) := Real.log_pos (by linarith)
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    simp only [List.map_cons, List.prod_cons]
    have hfac : 1 - 2 / (p : ℝ) + (p : ℝ) ^ (1 + 2 * d - 2) ≤ eulerLocal R U p := by
      unfold eulerLocal
      have e : (p : ℝ) ^ (1 + 2 * d - 2) = (p : ℝ) ^ (2 * d) / p := by
        rw [show 1 + 2 * d - 2 = 2 * d - 1 by ring, Real.rpow_sub hp0, Real.rpow_one]
      rw [e]
      have hrp : (p : ℝ) ^ (2 * d) ≤ Real.exp (2 * R * (Real.log p / Real.log (U - 1))) := by
        rw [Real.rpow_def_of_pos hp0]
        refine Real.exp_le_exp.mpr ?_
        have hd : d ≤ R / Real.log (U - 1) := by
          rw [le_div_iff₀ hlogU]
          exact hdU1
        calc Real.log p * (2 * d) ≤ Real.log p * (2 * (R / Real.log (U - 1))) :=
              mul_le_mul_of_nonneg_left (by linarith) hlogp
          _ = _ := by ring
      have := div_le_div_of_nonneg_right hrp hp0.le
      linarith
    have hnn : 0 ≤ (B.map fun p : ℕ => 1 - 2 / (p : ℝ) + (p : ℝ) ^ (1 + 2 * d - 2)).prod := by
      refine List.prod_nonneg ?_
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hB' q hq).two_le
      have h1 : 2 / (q : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hq2
      have : 0 ≤ (q : ℝ) ^ (1 + 2 * d - 2) := Real.rpow_nonneg (by linarith) _
      linarith
    exact mul_le_mul hfac (ih hB') hnn (eulerLocal_nonneg hp)

/-- **The second moment of `ζ` against a product of Euler factors.** For distinct primes with
`Π_{p ∈ B} p ≤ U^{21/50}`, on the upper blocks of `[U^{49/50}, U]` and the Levinson line `½ − d`,
`∫_a^v |ζ(z) Π_{p ∈ B}(1 − p^{−z})|² dτ ≤ (1 + F₀(U)) ((1+ε)(v−a) + ε a)`, where
`F₀(U) = eulerMain R U B ≈ (e^{2R}/(2R)) log U Π_{p ∈ B} (1 − 2/p + p^{2R/log U}/p)`. -/
theorem exists_euler_piece_second_moment_le {R : ℝ} (hR : 0 < R) {B : ℝ → List ℕ}
    (hprime : ∀ U, ∀ p ∈ B U, p.Prime) (hnodup : ∀ U, (B U).Nodup)
    (hlen : ∀ᶠ U in atTop, ((B U).prod : ℝ) ≤ U ^ ((21 : ℝ) / 50)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((49 : ℝ) / 50) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ) *
            ((B U).map fun p : ℕ => 1 - ((p : ℝ) : ℂ) ^ (-displacedLinePt d τ)).prod‖ ^ 2)
          ≤ (1 + eulerMain R U (B U)) * ((1 + ε) * (v - a) + ε * a) := by
  intro ε hε
  have hG0 : ∀ U, 0 ≤ ((B U).map (eulerLocal R U)).prod := fun U => by
    refine List.prod_nonneg ?_
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact eulerLocal_nonneg (hprime U q hq)
  have hmainNN : ∀ᶠ U : ℝ in atTop, 0 ≤ eulerMain R U (B U) := by
    filter_upwards [eventually_ge_atTop 3] with U hU
    have hlog : 0 < Real.log U := Real.log_pos (by linarith)
    unfold eulerMain
    have := hG0 U
    positivity
  have hbase := exists_twisted_second_moment_le hR (F := fun U => 1 + eulerMain R U (B U))
    (fun U => (B U).prod) (fun U => eulerCoeff (B U)) hlen
    (fun U n _ => abs_eulerCoeff_le (hprime U) (hnodup U) n)
    (by
      filter_upwards [hmainNN] with U hU
      linarith)
    (by
      filter_upwards [eventually_ge_atTop 3, hmainNN] with U hU3 hNN d hd hd8 hRd hdU1 a v η hη h4
        hav hvU hηa haη haU
      have hS : gcdSum₂ d (B U).prod (eulerCoeff (B U)) ≤ ((B U).map (eulerLocal R U)).prod := by
        rw [gcdSum₂_eq_gcdForm, gcdForm_eulerCoeff (hprime U) (hnodup U)]
        exact prod_local_le (hprime U) hU3 hdU1
      have h := mainTerm_le_of_gcdSum_le hR hd hd8 hRd hdU1 hU3 hη h4 hav hvU hηa haη haU (hG0 U) hS
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      unfold eulerMain at hNN ⊢
      linarith)
    ε hε
  filter_upwards [hbase] with U hU d hd hd8 hRd hdU a v ha haU hav hv2 hvU
  have h := hU d hd hd8 hRd hdU a v ha haU hav hv2 hvU
  simp_rw [edPoly_eulerCoeff (hprime U)] at h
  exact h

end GaloisForLFunctions.MultiscaleMollifiedZetaField
