import GaloisForLFunctions.HTGeometry.PhaseSignChain

/-!
# Sign chains at a shifted level, and chains that miss a prescribed finite set

`PhaseSignChain` builds its chain from the first hitting times of the levels `m₀π`.  Nothing forces
those levels to be integer multiples of `π`: any base level `c₀` with `cos c₀ ≠ 0` works, because
`cos (c₀ + iπ) = (-1)^i cos c₀` still alternates in sign and never vanishes.

That freedom is what removes an unwanted coincidence.  When the real part being counted is a
*product* of the polar factor with a real amplitude that has finitely many zeros, the nodes of the
chain must avoid those zeros.  Since the node at step `i` satisfies `φ (g i) = c₀ + iπ` exactly, a
node lands on a prescribed point `τ` only for the finitely many base levels `φ τ - iπ`.  Removing
those, together with the countably many zeros of `cos`, still leaves a base level in any window of
length `π` — so one extra half-turn of phase buys a chain entirely off the bad set.
-/

open Set

noncomputable section

namespace RHTower

variable {a b : ℝ}

/-- **A phase increase of `nπ` above a base level forces `n` sign changes.** -/
theorem exists_sign_chain_of_phase_increase_level {φ ρ : ℝ → ℝ} {c₀ : ℝ} {n : ℕ}
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) (hρ : ∀ τ ∈ Icc a b, 0 < ρ τ)
    (hcos : Real.cos c₀ ≠ 0)
    (hlow : φ a ≤ c₀) (hhigh : c₀ + (n : ℝ) * Real.pi ≤ φ b) :
    ∃ g : ℕ → ℝ, (∀ i ≤ n, g i ∈ Icc a b) ∧ (∀ i < n, g i < g (i + 1)) ∧
      (∀ i ≤ n, φ (g i) = c₀ + (i : ℝ) * Real.pi) ∧
      (∀ i < n,
        (ρ (g i) * Real.cos (φ (g i))) * (ρ (g (i + 1)) * Real.cos (φ (g (i + 1)))) < 0) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set c : ℕ → ℝ := fun i => c₀ + (i : ℝ) * Real.pi with hc
  have hstepAll : ∀ i : ℕ, c (i + 1) = c i + Real.pi := by
    intro i; simp only [hc]; push_cast; ring
  have hsqAll : ∀ i : ℕ, Real.cos (c i) ^ 2 = Real.cos c₀ ^ 2 := by
    intro i
    induction i with
    | zero => simp [hc]
    | succ j ih =>
        rw [hstepAll j, Real.cos_add_pi, neg_pow]
        simpa using ih
  have hcmono : ∀ i j : ℕ, i ≤ j → c i ≤ c j := by
    intro i j hij
    have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    simp only [hc]
    nlinarith
  have hhigh_i : ∀ i ≤ n, c i ≤ φ b := fun i hi => le_trans (hcmono i n hi) hhigh
  have hlow_i : ∀ i : ℕ, φ a ≤ c i := by
    intro i
    refine le_trans hlow ?_
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    simp only [hc]
    nlinarith
  set g : ℕ → ℝ := fun i => firstHit φ a b (c i) with hg
  have hgmem : ∀ i ≤ n, g i ∈ Icc a b := fun i hi =>
    (firstHit_mem hab hφ (hhigh_i i hi)).1
  have hgphase : ∀ i ≤ n, φ (g i) = c i := fun i hi =>
    firstHit_phase hab hφ (hlow_i i) (hhigh_i i hi)
  refine ⟨g, hgmem, ?_, hgphase, ?_⟩
  · intro i hi
    have hle : g i ≤ g (i + 1) :=
      firstHit_mono hab (hcmono i (i + 1) (by omega)) (hhigh_i (i + 1) (by omega))
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso
      have h1 : φ (g i) = c i := hgphase i (by omega)
      have h2 : φ (g (i + 1)) = c (i + 1) := hgphase (i + 1) (by omega)
      rw [heq, h2] at h1
      simp only [hc] at h1
      push_cast at h1
      nlinarith
    · exact hlt
  · intro i hi
    have h1 : φ (g i) = c i := hgphase i (by omega)
    have h2 : φ (g (i + 1)) = c (i + 1) := hgphase (i + 1) (by omega)
    have hcosstep : Real.cos (c (i + 1)) = -Real.cos (c i) := by
      rw [hstepAll i, Real.cos_add_pi]
    have hsqpos : 0 < Real.cos (c i) ^ 2 := by
      rw [hsqAll i]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hcos))
    have hρ1 : 0 < ρ (g i) := hρ _ (hgmem i (by omega))
    have hρ2 : 0 < ρ (g (i + 1)) := hρ _ (hgmem (i + 1) (by omega))
    rw [h1, h2, hcosstep]
    nlinarith [hsqpos, hρ1, hρ2, mul_pos hρ1 hρ2]

/-- The zeros of `cos` form a countable set. -/
theorem countable_cos_zero : Set.Countable {c : ℝ | Real.cos c = 0} := by
  have hsub : {c : ℝ | Real.cos c = 0}
      ⊆ Set.range (fun k : ℤ => (2 * (k : ℝ) + 1) * Real.pi / 2) := by
    intro c hc
    rw [Set.mem_setOf_eq, Real.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    exact ⟨k, hk.symm⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

/-- **A usable base level.**  In any window of length at least `π` there is a level at which `cos`
does not vanish and whose `π`-translates miss the finitely many prescribed phase values. -/
theorem exists_avoiding_level (φ : ℝ → ℝ) (S : Finset ℝ) (n : ℕ) {A B : ℝ}
    (hAB : A + Real.pi ≤ B) :
    ∃ c₀ : ℝ, A ≤ c₀ ∧ c₀ ≤ B ∧ Real.cos c₀ ≠ 0 ∧
      ∀ τ ∈ S, ∀ i : ℕ, i ≤ n → φ τ ≠ c₀ + (i : ℝ) * Real.pi := by
  classical
  set F : Finset ℝ :=
    (S ×ˢ Finset.range (n + 1)).image (fun p : ℝ × ℕ => φ p.1 - (p.2 : ℝ) * Real.pi) with hF
  have hcount : Set.Countable ({c : ℝ | Real.cos c = 0} ∪ (F : Set ℝ)) :=
    countable_cos_zero.union F.countable_toSet
  have hdense : Dense ({c : ℝ | Real.cos c = 0} ∪ (F : Set ℝ))ᶜ :=
    Countable.dense_compl ℝ hcount
  have hAB' : A < B := by linarith [Real.pi_pos]
  obtain ⟨c₀, hc₀mem, hc₀I⟩ :=
    hdense.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hAB')
  refine ⟨c₀, hc₀I.1.le, hc₀I.2.le, ?_, ?_⟩
  · intro hcos
    exact hc₀mem (Or.inl hcos)
  · intro τ hτ i hi hval
    refine hc₀mem (Or.inr ?_)
    rw [hF]
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
      Finset.mem_range]
    exact ⟨(τ, i), ⟨hτ, by omega⟩, by rw [hval]; ring⟩

/-- **A sign chain whose nodes miss a prescribed finite set.**  One extra half-turn of phase buys
the freedom to place every node off `S`. -/
theorem exists_sign_chain_avoiding {φ ρ : ℝ → ℝ} {n : ℕ} (S : Finset ℝ)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) (hρ : ∀ τ ∈ Icc a b, 0 < ρ τ)
    (hadv : φ a + ((n : ℝ) + 1) * Real.pi ≤ φ b) :
    ∃ g : ℕ → ℝ, (∀ i ≤ n, g i ∈ Icc a b) ∧ (∀ i < n, g i < g (i + 1)) ∧
      (∀ i ≤ n, g i ∉ S) ∧
      (∀ i < n,
        (ρ (g i) * Real.cos (φ (g i))) * (ρ (g (i + 1)) * Real.cos (φ (g (i + 1)))) < 0) := by
  obtain ⟨c₀, hc₀low, hc₀high, hcos, havoid⟩ :=
    exists_avoiding_level φ S n (A := φ a) (B := φ b - (n : ℝ) * Real.pi) (by linarith)
  obtain ⟨g, hgmem, hgstep, hgphase, hgsign⟩ :=
    exists_sign_chain_of_phase_increase_level (φ := φ) (ρ := ρ) (c₀ := c₀) (n := n)
      hab hφ hρ hcos hc₀low (by linarith)
  refine ⟨g, hgmem, hgstep, ?_, hgsign⟩
  intro i hi hmem
  exact havoid (g i) hmem i hi (hgphase i hi)

end RHTower

end
