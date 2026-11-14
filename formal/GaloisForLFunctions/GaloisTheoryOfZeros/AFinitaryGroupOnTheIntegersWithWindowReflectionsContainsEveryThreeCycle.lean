import Mathlib

/-!
# A finitary group on the integers with window reflections contains every 3-cycle

Let `H` be a group of permutations of `ℤ`, each moving finitely many integers, such that for
every `K` some elements of `H` act on the window `[-K, K]` as the reflections `m ↦ -m - 1` and
`m ↦ -m`. No element of `H` is a reflection, but `H` contains every 3-cycle
(`hasCycle_of_windowReflections`).

Proof. The products of the window reflections are translations on windows, so the set of triples
carrying a 3-cycle of `H` is stable under translations and reflections. One 3-cycle is the
commutator of a nontrivial element `g` and its translate by the width of the support of `g`: the
two supports meet in one point (`commutator_apply_of_supports_meet`). Two 3-cycles of `H` that
share a point give a third one by conjugation (`HasCycle.exchange`). With the reflected triple
this is the Euclidean algorithm on the two gaps of a triple, down to gaps `(d, d)`
(`hasCycle_gcd`), and then every triple of one class modulo `d` carries a 3-cycle
(`hasCycle_class`). A translation on the window `{0}` moves finitely many integers, so it carries
a triple `{0, nd, (n+1)d}` far out to `{-1, nd, (n+1)d}`, whose gaps are coprime: `d = 1`.
-/

open Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

theorem perm_apply_inv_self {α : Type*} (f : Perm α) (x : α) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem perm_inv_apply_self {α : Type*} (f : Perm α) (x : α) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

/-! ## The commutator of two permutations whose supports meet in one point -/

/-- If `x` is the only point moved by both `σ` and `τ`, the commutator `σ τ σ⁻¹ τ⁻¹` is the
3-cycle `x → σ x → τ x → x`. -/
theorem commutator_apply_of_supports_meet {α : Type*} (σ τ : Perm α) {x : α} (hσ : σ x ≠ x)
    (hτ : τ x ≠ x) (h : ∀ m, σ m ≠ m → τ m ≠ m → m = x) :
    (σ * τ * σ⁻¹ * τ⁻¹) x = σ x ∧ (σ * τ * σ⁻¹ * τ⁻¹) (σ x) = τ x ∧
      (σ * τ * σ⁻¹ * τ⁻¹) (τ x) = x ∧
      ∀ w, w ≠ x → w ≠ σ x → w ≠ τ x → (σ * τ * σ⁻¹ * τ⁻¹) w = w := by
  have hσfix : ∀ m, m ≠ x → τ m ≠ m → σ m = m := fun m hm hτm => by
    by_contra hσm
    exact hm (h m hσm hτm)
  have hτfix : ∀ m, m ≠ x → σ m ≠ m → τ m = m := fun m hm hσm => by
    by_contra hτm
    exact hm (h m hσm hτm)
  have inv_fix : ∀ (ρ : Perm α) (m : α), ρ m = m → ρ⁻¹ m = m := fun ρ m hm => by
    rw [Perm.inv_eq_iff_eq]
    exact hm.symm
  have key : ∀ w, (σ * τ * σ⁻¹ * τ⁻¹) w = σ (τ (σ⁻¹ (τ⁻¹ w))) := fun _ => rfl
  refine ⟨?_, ?_, ?_, fun w hwx hwσ hwτ => ?_⟩
  · obtain ⟨y, hy⟩ : ∃ y, τ⁻¹ x = y := ⟨_, rfl⟩
    have hτy : τ y = x := by rw [← hy, perm_apply_inv_self]
    have hyx : y ≠ x := fun e => hτ (by rw [e] at hτy; exact hτy)
    have hσy : σ y = y := hσfix y hyx (by rw [hτy]; exact Ne.symm hyx)
    rw [key, hy, inv_fix σ y hσy, hτy]
  · have h1 : τ (σ x) = σ x := hτfix (σ x) hσ fun e => hσ (σ.injective e)
    have h2 : σ (τ x) = τ x := hσfix (τ x) hτ fun e => hτ (τ.injective e)
    rw [key, inv_fix τ _ h1, perm_inv_apply_self, h2]
  · obtain ⟨z, hz⟩ : ∃ z, σ⁻¹ x = z := ⟨_, rfl⟩
    have hσz : σ z = x := by rw [← hz, perm_apply_inv_self]
    have hzx : z ≠ x := fun e => hσ (by rw [e] at hσz; exact hσz)
    have hτz : τ z = z := hτfix z hzx (by rw [hσz]; exact Ne.symm hzx)
    rw [key, perm_inv_apply_self, hz, hτz, hσz]
  · by_cases hτw : τ w = w
    · obtain ⟨v, hv⟩ : ∃ v, σ⁻¹ w = v := ⟨_, rfl⟩
      have hσv : σ v = w := by rw [← hv, perm_apply_inv_self]
      rw [key, inv_fix τ w hτw, hv]
      by_cases hfix : σ v = v
      · have hvw : v = w := hfix.symm.trans hσv
        rw [hvw, hτw, ← hvw, hfix]
      · have hvx : v ≠ x := fun e => hwσ (by rw [← hσv, e])
        rw [hτfix v hvx hfix, hσv]
    · have hσw : σ w = w := hσfix w hwx hτw
      obtain ⟨u, hu⟩ : ∃ u, τ⁻¹ w = u := ⟨_, rfl⟩
      have hτu : τ u = w := by rw [← hu, perm_apply_inv_self]
      have hux : u ≠ x := fun e => hwτ (by rw [← hτu, e])
      have hτu' : τ u ≠ u := fun e => hτw (by
        have huw : u = w := e.symm.trans hτu
        rw [← huw, e])
      rw [key, hu, inv_fix σ u (hσfix u hux hτu'), hτu, hσw]

/-! ## The 3-cycles of a group of permutations -/

/-- The group `H` contains the 3-cycle `i → j → k → i`. -/
def HasCycle {α : Type*} (H : Subgroup (Perm α)) (i j k : α) : Prop :=
  i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    ∃ T ∈ H, T i = j ∧ T j = k ∧ T k = i ∧ ∀ x, x ≠ i → x ≠ j → x ≠ k → T x = x

section Cycles

variable {α : Type*} {H : Subgroup (Perm α)} {i j k : α}

theorem HasCycle.rot (h : HasCycle H i j k) : HasCycle H j k i := by
  obtain ⟨hij, hjk, hik, T, hT, h1, h2, h3, h4⟩ := h
  exact ⟨hjk, hik.symm, hij.symm, T, hT, h2, h3, h1, fun x hx1 hx2 hx3 => h4 x hx3 hx1 hx2⟩

/-- The inverse cycle. -/
theorem HasCycle.inv (h : HasCycle H i j k) : HasCycle H i k j := by
  obtain ⟨hij, hjk, hik, T, hT, h1, h2, h3, h4⟩ := h
  refine ⟨hik, hjk.symm, hij, T⁻¹, H.inv_mem hT, ?_, ?_, ?_, fun x hx1 hx2 hx3 => ?_⟩
  · rw [Perm.inv_eq_iff_eq]
    exact h3.symm
  · rw [Perm.inv_eq_iff_eq]
    exact h2.symm
  · rw [Perm.inv_eq_iff_eq]
    exact h1.symm
  · rw [Perm.inv_eq_iff_eq]
    exact (h4 x hx1 hx3 hx2).symm

/-- Conjugation by `g` carries the cycle on `(i, j, k)` to the cycle on `(g i, g j, g k)`. -/
theorem HasCycle.conj (h : HasCycle H i j k) {g : Perm α} (hg : g ∈ H) :
    HasCycle H (g i) (g j) (g k) := by
  obtain ⟨hij, hjk, hik, T, hT, h1, h2, h3, h4⟩ := h
  refine ⟨g.injective.ne hij, g.injective.ne hjk, g.injective.ne hik, g * T * g⁻¹,
    H.mul_mem (H.mul_mem hg hT) (H.inv_mem hg), ?_, ?_, ?_, fun x hx1 hx2 hx3 => ?_⟩
  · show g (T (g⁻¹ (g i))) = g j
    rw [perm_inv_apply_self, h1]
  · show g (T (g⁻¹ (g j))) = g k
    rw [perm_inv_apply_self, h2]
  · show g (T (g⁻¹ (g k))) = g i
    rw [perm_inv_apply_self, h3]
  · have e : ∀ y, x ≠ g y → g⁻¹ x ≠ y := fun y hy e' => hy (by rw [← e', perm_apply_inv_self])
    show g (T (g⁻¹ x)) = x
    rw [h4 _ (e i hx1) (e j hx2) (e k hx3), perm_apply_inv_self]

/-- **Exchange.** If `H` contains a cycle on `{a, c, d}` and a cycle on a triple that contains
`a` and a point `b` outside `{a, c, d}`, it contains a cycle on `{b, c, d}`: conjugate the first
by the second, read in the direction that keeps `c` and `d` in the triple. -/
theorem HasCycle.exchange {a b c d e : α} (hA : HasCycle H a c d) (hB : HasCycle H a b e)
    (hbc : b ≠ c) (hbd : b ≠ d) : HasCycle H b c d := by
  by_cases hec : e = c
  · subst hec
    obtain ⟨-, -, -, T, hT, t1, t2, -, t4⟩ := hB.inv
    have := hA.conj hT
    rw [t1, t2, t4 d hA.2.2.1.symm hA.2.1.symm hbd.symm] at this
    exact this.rot.inv
  by_cases hed : e = d
  · subst hed
    obtain ⟨-, -, -, T, hT, t1, t2, -, t4⟩ := hB.inv
    have := hA.conj hT
    rw [t1, t4 c hA.1.symm hA.2.1 hbc.symm, t2] at this
    exact this.inv.rot
  · obtain ⟨-, -, -, T, hT, t1, -, -, t4⟩ := hB
    have := hA.conj hT
    rw [t1, t4 c hA.1.symm hbc.symm (Ne.symm hec),
      t4 d hA.2.2.1.symm hbd.symm (Ne.symm hed)] at this
    exact this

end Cycles

/-- A property of triples of distinct integers that is symmetric and holds for increasing
triples holds for all triples. -/
theorem forall_of_forall_lt {P : ℤ → ℤ → ℤ → Prop} (rot : ∀ i j k, P i j k → P j k i)
    (inv : ∀ i j k, P i j k → P i k j) (h : ∀ a b c, a < b → b < c → P a b c)
    {a b c : ℤ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : P a b c := by
  rcases lt_or_gt_of_ne hab with h1 | h1
  · rcases lt_or_gt_of_ne hbc with h2 | h2
    · exact h a b c h1 h2
    · rcases lt_or_gt_of_ne hac with h3 | h3
      · exact inv _ _ _ (h a c b h3 h2)
      · exact rot _ _ _ (h c a b h3 h1)
  · rcases lt_or_gt_of_ne hbc with h2 | h2
    · rcases lt_or_gt_of_ne hac with h3 | h3
      · exact inv _ _ _ (rot _ _ _ (h b a c h1 h3))
      · exact rot _ _ _ (rot _ _ _ (h b c a h2 h3))
    · exact rot _ _ _ (inv _ _ _ (h c b a h2 h1))

/-! ## Chains of 3-cycles -/

section Chain

variable {H : Subgroup (Perm ℤ)} {f : ℤ → ℤ}

theorem hasCycle_of_chain_one (hf : Function.Injective f)
    (h : ∀ n, HasCycle H (f n) (f (n + 1)) (f (n + 2))) (q : ℕ) :
    ∀ a : ℤ, HasCycle H (f a) (f (a + 1)) (f (a + 2 + q)) := by
  induction q with
  | zero =>
    intro a
    rw [Nat.cast_zero, add_zero]
    exact h a
  | succ q ih =>
    intro a
    have hB : HasCycle H (f (a + 2 + q)) (f (a + q + 3)) (f (a + q + 1)) := by
      have := (h (a + q + 1)).rot
      rwa [show a + q + 1 + 1 = a + 2 + q by ring, show a + q + 1 + 2 = a + q + 3 by ring] at this
    have := ((ih a).rot.rot.exchange hB (hf.ne (by omega)) (hf.ne (by omega))).rot
    rw [show a + 2 + ((q + 1 : ℕ) : ℤ) = a + q + 3 by omega]
    exact this

theorem hasCycle_of_chain (hf : Function.Injective f)
    (h : ∀ n, HasCycle H (f n) (f (n + 1)) (f (n + 2))) (p : ℕ) :
    ∀ (q : ℕ) (a : ℤ), HasCycle H (f a) (f (a + 1 + p)) (f (a + 2 + p + q)) := by
  induction p with
  | zero =>
    intro q a
    rw [Nat.cast_zero, add_zero, add_zero]
    exact hasCycle_of_chain_one hf h q a
  | succ p ih =>
    intro q a
    have hA : HasCycle H (f (a + 1 + p)) (f (a + p + q + 3)) (f a) := by
      have := (ih (q + 1) a).rot
      rwa [show a + 2 + (p : ℤ) + ((q + 1 : ℕ) : ℤ) = a + p + q + 3 by omega] at this
    have := (hA.exchange (h (a + 1 + p)) (hf.ne (by omega)) (hf.ne (by omega))).rot.rot
    rw [show a + 1 + ((p + 1 : ℕ) : ℤ) = a + 1 + p + 1 by omega,
      show a + 2 + ((p + 1 : ℕ) : ℤ) + (q : ℤ) = a + p + q + 3 by omega]
    exact this

/-- **A chain of 3-cycles gives all 3-cycles.** If `H` contains the cycles on the triples
`(f n, f (n+1), f (n+2))` of an injective sequence, it contains the cycle on `(f a, f b, f c)`
for `a < b < c`. -/
theorem hasCycle_of_chain_lt (hf : Function.Injective f)
    (h : ∀ n, HasCycle H (f n) (f (n + 1)) (f (n + 2))) {a b c : ℤ} (hab : a < b)
    (hbc : b < c) : HasCycle H (f a) (f b) (f c) := by
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ b - a - 1 by omega)
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c - b - 1 by omega)
  have := hasCycle_of_chain hf h p q a
  rwa [show a + 1 + (p : ℤ) = b by omega, show a + 2 + (p : ℤ) + q = c by omega] at this

end Chain

/-! ## Window reflections -/

/-- For every `K`, elements of `H` act on the window `[-K, K]` as `m ↦ -m - 1` and `m ↦ -m`. -/
def HasWindowReflections (H : Subgroup (Perm ℤ)) : Prop :=
  ∀ K : ℤ, ∃ a ∈ H, ∃ b ∈ H, ∀ m : ℤ, |m| ≤ K → a m = -m - 1 ∧ b m = -m

section Windows

variable {H : Subgroup (Perm ℤ)}

theorem exists_window_shift_nat (hwin : HasWindowReflections H) (n : ℕ) :
    ∀ K : ℤ, (∃ h ∈ H, ∀ m : ℤ, |m| ≤ K → h m = m + n) ∧
      ∃ h ∈ H, ∀ m : ℤ, |m| ≤ K → h m = m - n := by
  induction n with
  | zero =>
    intro K
    exact ⟨⟨1, H.one_mem, fun m _ => by simp⟩, ⟨1, H.one_mem, fun m _ => by simp⟩⟩
  | succ n ih =>
    intro K
    obtain ⟨⟨h₁, hh₁, e₁⟩, ⟨h₂, hh₂, e₂⟩⟩ := ih K
    obtain ⟨a, ha, b, hb, hab⟩ := hwin (K + n + 1)
    refine ⟨⟨b * a * h₁, H.mul_mem (H.mul_mem hb ha) hh₁, fun m hm => ?_⟩,
      ⟨a * b * h₂, H.mul_mem (H.mul_mem ha hb) hh₂, fun m hm => ?_⟩⟩
    · have hm' := abs_le.mp hm
      have h1 : |m + (n : ℤ)| ≤ K + n + 1 := by
        rw [abs_le]
        constructor <;> omega
      have h2 : |-(m + (n : ℤ)) - 1| ≤ K + n + 1 := by
        rw [abs_le]
        constructor <;> omega
      show b (a (h₁ m)) = m + ((n + 1 : ℕ) : ℤ)
      rw [e₁ m hm, (hab _ h1).1, (hab _ h2).2]
      omega
    · have hm' := abs_le.mp hm
      have h1 : |m - (n : ℤ)| ≤ K + n + 1 := by
        rw [abs_le]
        constructor <;> omega
      have h2 : |-(m - (n : ℤ))| ≤ K + n + 1 := by
        rw [abs_le]
        constructor <;> omega
      show a (b (h₂ m)) = m - ((n + 1 : ℕ) : ℤ)
      rw [e₂ m hm, (hab _ h1).2, (hab _ h2).1]
      omega

/-- The translation by `c` on the window `[-K, K]`. -/
theorem exists_window_shift (hwin : HasWindowReflections H) (K c : ℤ) :
    ∃ h ∈ H, ∀ m : ℤ, |m| ≤ K → h m = m + c := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · exact (exists_window_shift_nat hwin n K).1
  · obtain ⟨h, hh, e⟩ := (exists_window_shift_nat hwin n K).2
    exact ⟨h, hh, fun m hm => by rw [e m hm]; ring⟩

/-- The reflection `m ↦ c - m` on the window `[-K, K]`. -/
theorem exists_window_reflection (hwin : HasWindowReflections H) (K c : ℤ) :
    ∃ h ∈ H, ∀ m : ℤ, |m| ≤ K → h m = c - m := by
  obtain ⟨_, -, b, hb, hab⟩ := hwin K
  obtain ⟨h, hh, e⟩ := exists_window_shift hwin K c
  refine ⟨h * b, H.mul_mem hh hb, fun m hm => ?_⟩
  show h (b m) = c - m
  rw [(hab m hm).2, e (-m) (by rwa [abs_neg])]
  ring

theorem HasCycle.shift (hwin : HasWindowReflections H) {i j k : ℤ} (h : HasCycle H i j k)
    (c : ℤ) : HasCycle H (i + c) (j + c) (k + c) := by
  obtain ⟨g, hg, e⟩ := exists_window_shift hwin (|i| + |j| + |k|) c
  have := h.conj hg
  rwa [e i (by linarith [abs_nonneg j, abs_nonneg k]),
    e j (by linarith [abs_nonneg i, abs_nonneg k]),
    e k (by linarith [abs_nonneg i, abs_nonneg j])] at this

theorem HasCycle.reflect (hwin : HasWindowReflections H) {i j k : ℤ} (h : HasCycle H i j k)
    (c : ℤ) : HasCycle H (c - i) (c - j) (c - k) := by
  obtain ⟨g, hg, e⟩ := exists_window_reflection hwin (|i| + |j| + |k|) c
  have := h.conj hg
  rwa [e i (by linarith [abs_nonneg j, abs_nonneg k]),
    e j (by linarith [abs_nonneg i, abs_nonneg k]),
    e k (by linarith [abs_nonneg i, abs_nonneg j])] at this

/-- **The Euclidean algorithm on the gaps of a triple.** A cycle on a triple with gaps
`(α, β)` gives a cycle on a triple with gaps `(d, d)`, `d = gcd α β`: the exchange with the
reflected triple replaces the gaps by `(min α β, |α - β|)`. -/
theorem hasCycle_gcd (hwin : HasWindowReflections H) :
    ∀ n α β : ℕ, 0 < α → 0 < β → α + β ≤ n → HasCycle H 0 (α : ℤ) ((α : ℤ) + β) →
      HasCycle H 0 ((Nat.gcd α β : ℕ) : ℤ) (2 * ((Nat.gcd α β : ℕ) : ℤ)) := by
  intro n
  induction n with
  | zero =>
    intro α β hα hβ hle
    omega
  | succ n ih =>
    intro α β hα hβ hle h
    have hrefl : HasCycle H ((α : ℤ) + β) (β : ℤ) 0 := by
      have := h.reflect hwin ((α : ℤ) + β)
      rwa [sub_zero, add_sub_cancel_left, sub_self] at this
    rcases lt_trichotomy α β with hlt | heq | hgt
    · obtain ⟨δ, rfl⟩ : ∃ δ, β = δ + α := ⟨β - α, by omega⟩
      have hE := h.rot.rot.exchange hrefl (by omega) (by omega)
      have h' : HasCycle H 0 (α : ℤ) ((α : ℤ) + δ) := by
        have := hE.rot
        rwa [show ((δ + α : ℕ) : ℤ) = (α : ℤ) + δ by omega] at this
      have := ih α δ hα (by omega) (by omega) h'
      rwa [Nat.gcd_add_self_right]
    · subst heq
      rw [Nat.gcd_self]
      rwa [show (α : ℤ) + α = 2 * α by ring] at h
    · obtain ⟨δ, rfl⟩ : ∃ δ, α = δ + β := ⟨α - β, by omega⟩
      have hE := h.rot.rot.exchange hrefl (by omega) (by omega)
      have h' : HasCycle H 0 (β : ℤ) ((β : ℤ) + δ) := by
        have := hE.inv.rot.rot
        rwa [show ((δ + β : ℕ) : ℤ) = (β : ℤ) + δ by omega] at this
      have := ih β δ hβ (by omega) (by omega) h'
      rwa [Nat.gcd_comm, Nat.gcd_add_self_right]

/-- **The cycles of one class.** A cycle on `{0, d, 2d}` gives the cycle on every triple of one
class modulo `d`. -/
theorem hasCycle_class (hwin : HasWindowReflections H) {d : ℕ} (hd : 0 < d)
    (h : HasCycle H 0 (d : ℤ) (2 * (d : ℤ))) (i₀ : ℤ) {a b c : ℤ} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : HasCycle H (i₀ + a * d) (i₀ + b * d) (i₀ + c * d) := by
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hf : Function.Injective fun n : ℤ => i₀ + n * d := fun x y hxy => by
    have hxy' : i₀ + x * (d : ℤ) = i₀ + y * d := hxy
    exact mul_right_cancel₀ hd0 (add_left_cancel hxy')
  have hch : ∀ n : ℤ, HasCycle H (i₀ + n * d) (i₀ + (n + 1) * d) (i₀ + (n + 2) * d) := fun n => by
    have := h.shift hwin (i₀ + n * d)
    rwa [zero_add, show (d : ℤ) + (i₀ + n * d) = i₀ + (n + 1) * d by ring,
      show 2 * (d : ℤ) + (i₀ + n * d) = i₀ + (n + 2) * d by ring] at this
  exact forall_of_forall_lt
    (P := fun a b c => HasCycle H (i₀ + a * d) (i₀ + b * d) (i₀ + c * d))
    (fun _ _ _ h => h.rot) (fun _ _ _ h => h.inv)
    (fun a b c hab hbc => hasCycle_of_chain_lt (f := fun n : ℤ => i₀ + n * d) hf hch hab hbc)
    hab hbc hac

variable (hfin : ∀ g ∈ H, {m : ℤ | g m ≠ m}.Finite)
include hfin

/-- A translation on the window `{0}` moves finitely many integers: it carries a cycle on
`{0, j, k}` far out to a cycle on `{-1, j, k}`. -/
theorem exists_break (hwin : HasWindowReflections H) :
    ∃ L : ℤ, ∀ j k, L ≤ j → L ≤ k → HasCycle H 0 j k → HasCycle H (-1) j k := by
  obtain ⟨y, hy, e⟩ := exists_window_shift hwin 0 (-1)
  obtain ⟨M, hM⟩ := (hfin y hy).bddAbove
  have fix : ∀ m, M + 1 ≤ m → y m = m := fun m hm => by
    by_contra hne
    have : m ≤ M := hM hne
    omega
  refine ⟨M + 1, fun j k hj hk h => ?_⟩
  have := h.conj hy
  rwa [e 0 (by simp), zero_add, fix j hj, fix k hk] at this

/-- **One 3-cycle.** The commutator of a nontrivial element and its translate by the width of
its support. -/
theorem exists_hasCycle (hwin : HasWindowReflections H) : ∃ i j k, HasCycle H i j k := by
  obtain ⟨g, hg, _, -, hab⟩ := hwin 0
  have hg0 : g 0 ≠ 0 := by
    rw [(hab 0 (by simp)).1]
    norm_num
  obtain ⟨m₀, hm₀, hmin⟩ := Set.exists_min_image {m : ℤ | g m ≠ m} id (hfin g hg) ⟨0, hg0⟩
  obtain ⟨m₁, hm₁, hmax⟩ := Set.exists_max_image {m : ℤ | g m ≠ m} id (hfin g hg) ⟨0, hg0⟩
  obtain ⟨h, hh, e⟩ := exists_window_shift hwin (|m₀| + |m₁|) (m₀ - m₁)
  have hhm₁ : h m₁ = m₀ := by
    rw [e m₁ (by linarith [abs_nonneg m₀])]
    ring
  have hinv : h⁻¹ m₀ = m₁ := Perm.inv_eq_iff_eq.mpr hhm₁.symm
  have hgm₀ : g m₀ ≠ m₀ := hm₀
  have hg'm₀ : (h * g * h⁻¹) m₀ ≠ m₀ := by
    show h (g (h⁻¹ m₀)) ≠ m₀
    rw [hinv]
    intro e'
    exact hm₁ (h.injective (e'.trans hhm₁.symm))
  -- the supports of `g` and of its translate meet in `m₀`
  have key : ∀ m, g m ≠ m → (h * g * h⁻¹) m ≠ m → m = m₀ := by
    intro m hm hm'
    have hy : g (h⁻¹ m) ≠ h⁻¹ m := by
      intro hfix
      apply hm'
      show h (g (h⁻¹ m)) = m
      rw [hfix, perm_apply_inv_self]
    have hyle : h⁻¹ m ≤ m₁ := hmax _ hy
    have hyge : m₀ ≤ h⁻¹ m := hmin _ hy
    have hmge : m₀ ≤ m := hmin _ hm
    have hshift : h (h⁻¹ m) = h⁻¹ m + (m₀ - m₁) :=
      e _ (abs_le.mpr ⟨by linarith [neg_abs_le m₀, abs_nonneg m₁],
        by linarith [le_abs_self m₁, abs_nonneg m₀]⟩)
    rw [perm_apply_inv_self] at hshift
    exact le_antisymm (by linarith) hmge
  obtain ⟨c1, c2, c3, c4⟩ := commutator_apply_of_supports_meet g (h * g * h⁻¹) hgm₀ hg'm₀ key
  have hg' : h * g * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh)
  refine ⟨m₀, g m₀, (h * g * h⁻¹) m₀, Ne.symm hgm₀, fun e' => ?_, Ne.symm hg'm₀,
    g * (h * g * h⁻¹) * g⁻¹ * (h * g * h⁻¹)⁻¹,
    H.mul_mem (H.mul_mem (H.mul_mem hg hg') (H.inv_mem hg)) (H.inv_mem hg'), c1, c2, c3, c4⟩
  have h1 : g (g m₀) ≠ g m₀ := fun e'' => hgm₀ (g.injective e'')
  have h2 : (h * g * h⁻¹) (g m₀) ≠ g m₀ := by
    rw [e']
    exact fun e'' => hg'm₀ ((h * g * h⁻¹).injective e'')
  exact hgm₀ (key _ h1 h2)

/-- **A finitary group on the integers with window reflections contains every 3-cycle.** -/
theorem hasCycle_of_windowReflections (hwin : HasWindowReflections H) {i j k : ℤ} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) : HasCycle H i j k := by
  -- a cycle on a triple `0 < α < α + β`
  obtain ⟨i₀, j₀, k₀, h₀⟩ := exists_hasCycle hfin hwin
  obtain ⟨α, β, hα, hβ, hαβ⟩ :
      ∃ α β : ℕ, 0 < α ∧ 0 < β ∧ HasCycle H 0 (α : ℤ) ((α : ℤ) + β) := by
    refine forall_of_forall_lt
      (P := fun a b c => HasCycle H a b c →
        ∃ α β : ℕ, 0 < α ∧ 0 < β ∧ HasCycle H 0 (α : ℤ) ((α : ℤ) + β))
      (fun _ _ _ hP hc => hP hc.rot.rot) (fun _ _ _ hP hc => hP hc.inv)
      (fun a b c hab hbc hc => ?_) h₀.1 h₀.2.1 h₀.2.2.1 h₀
    obtain ⟨α, hα⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ b - a by omega)
    obtain ⟨β, hβ⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c - b by omega)
    refine ⟨α, β, by omega, by omega, ?_⟩
    have := hc.shift hwin (-a)
    rwa [show a + -a = 0 by ring, show b + -a = (α : ℤ) by omega,
      show c + -a = (α : ℤ) + β by omega] at this
  -- gaps `(d, d)`, and all triples of the class of `0` modulo `d`
  have hd := hasCycle_gcd hwin (α + β) α β hα hβ le_rfl hαβ
  have hdpos : 0 < Nat.gcd α β := Nat.gcd_pos_of_pos_left β hα
  generalize Nat.gcd α β = d at hd hdpos
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hdpos
  -- a triple of the class far out, moved off the class
  obtain ⟨L, hL⟩ := exists_break hfin hwin
  obtain ⟨n, hnL, hn⟩ : ∃ n : ℕ, L ≤ n ∧ 0 < n :=
    ⟨L.toNat + 1, by have := Int.self_le_toNat L; push_cast; linarith, Nat.succ_pos _⟩
  have hnd : (n : ℤ) ≤ n * d := le_mul_of_one_le_right (Nat.cast_nonneg n) hd1
  have h1 : HasCycle H 0 ((n : ℤ) * d) (((n : ℤ) + 1) * d) := by
    have := hasCycle_class hwin hdpos hd 0 (a := 0) (b := n) (c := n + 1)
      (by omega) (by omega) (by omega)
    simpa using this
  have h2 : HasCycle H (-1) ((n : ℤ) * d) (((n : ℤ) + 1) * d) :=
    hL _ _ (hnL.trans hnd) (by nlinarith) h1
  have h3 : HasCycle H 0 ((n * d + 1 : ℕ) : ℤ) (((n * d + 1 : ℕ) : ℤ) + d) := by
    have := h2.shift hwin 1
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num,
      show (n : ℤ) * d + 1 = ((n * d + 1 : ℕ) : ℤ) by simp,
      show ((n : ℤ) + 1) * d + 1 = ((n * d + 1 : ℕ) : ℤ) + d by push_cast; ring] at this
  -- its gaps are coprime
  have h4 := hasCycle_gcd hwin _ (n * d + 1) d (Nat.succ_pos _) hdpos le_rfl h3
  have hg : Nat.gcd (n * d + 1) d = 1 := by
    have e1 : Nat.gcd (n * d + 1) d ∣ n * d := (Nat.gcd_dvd_right _ _).mul_left n
    have e2 : Nat.gcd (n * d + 1) d ∣ n * d + 1 := Nat.gcd_dvd_left _ _
    exact Nat.dvd_one.mp ((Nat.dvd_add_right e1).mp e2)
  rw [hg] at h4
  have := hasCycle_class hwin Nat.one_pos h4 0 hij hjk hik
  simpa using this

end Windows

end GaloisForLFunctions.GaloisTheoryOfZeros
