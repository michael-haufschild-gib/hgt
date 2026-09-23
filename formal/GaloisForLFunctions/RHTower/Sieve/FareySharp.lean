import GaloisForLFunctions.RHTower.Sieve.LargeSieveCircleSharp

/-!
# The sharp large sieve at Farey points

The proper Farey fractions of order `Q` — reduced `a/q` with `1 ≤ a < q ≤ Q` — are `Q^{-2}`-separated
in `ℝ/ℤ` and lie in `[Q^{-1}, 1 - Q^{-1}]`, hence inside the window the sharp bound requires.  So

`∑_{a/q} |S(a/q)|² ≤ (Q² + 4πN) ∑_{n < N} |c_n|²`,

the classical `N + Q²` up to the absolute constant, with no logarithm.

The fraction `1/1` is excluded: its value is the endpoint `1`, which is the same point of `ℝ/ℤ` as
`0`, so no interval of the line can hold it together with the others while keeping them separated.
-/

namespace RHTower.Sieve

open Finset

/-- The proper Farey set: reduced `a/q` with `1 ≤ a < q ≤ Q`. -/
def properFareySet (Q : ℕ) : Finset (ℕ × ℕ) :=
  (fareySet Q).filter (fun p => p.1 < p.2)

open scoped Classical in
/-- Its values, as a finite set of reals. -/
noncomputable def properFareyReals (Q : ℕ) : Finset ℝ :=
  (properFareySet Q).image (fun p => (p.1 : ℝ) / (p.2 : ℝ))

theorem mem_properFareySet {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ properFareySet Q ↔ p ∈ fareySet Q ∧ p.1 < p.2 := by
  rw [properFareySet, Finset.mem_filter]

/-- **The sharp large sieve at Farey points.** -/
theorem largeSieve_farey_sharp (N : ℕ) (hN : 0 < N) {Q : ℕ} (hQ : 2 ≤ Q) (c : Fin N → ℂ) :
    ∑ x ∈ properFareyReals Q, ‖expSum N c x‖ ^ (2 : ℕ)
      ≤ ((Q : ℝ) ^ (2 : ℕ) + 4 * Real.pi * (N : ℝ)) * ∑ n : Fin N, ‖c n‖ ^ (2 : ℕ) := by
  classical
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  set δ : ℝ := 1 / (Q : ℝ) ^ (2 : ℕ) with hδdef
  have hδ : (0 : ℝ) < δ := by rw [hδdef]; positivity
  -- membership unpacked
  have hunpack : ∀ x ∈ properFareyReals Q, ∃ p ∈ properFareySet Q,
      (p.1 : ℝ) / (p.2 : ℝ) = x := by
    intro x hx
    rw [properFareyReals, Finset.mem_image] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, hp, hpx⟩
  -- the set is nonempty: `1/2` is a proper Farey fraction of every order at least two
  have hne : (properFareyReals Q).Nonempty := by
    refine ⟨(1 : ℝ) / (2 : ℝ), ?_⟩
    rw [properFareyReals, Finset.mem_image]
    refine ⟨(1, 2), ?_, by norm_num⟩
    rw [mem_properFareySet]
    refine ⟨?_, by norm_num⟩
    rw [mem_fareySet]
    refine ⟨⟨le_rfl, by omega⟩, ⟨by omega, hQ⟩, by omega, ?_⟩
    simp
  -- separation, inherited from the Farey separation on pairs
  have hsep : ∀ x ∈ properFareyReals Q, ∀ y ∈ properFareyReals Q, x ≠ y →
      δ ≤ toIntDist (x - y) := by
    intro x hx y hy hxy
    obtain ⟨p, hp, hpx⟩ := hunpack x hx
    obtain ⟨r, hr, hry⟩ := hunpack y hy
    have hpr : r ≠ p := by
      intro hcon
      rw [hcon] at hry
      exact hxy (hpx.symm.trans hry)
    have hps : p ∈ fareySet Q := (mem_properFareySet.mp hp).1
    have hrs : r ∈ fareySet Q := (mem_properFareySet.mp hr).1
    have := fareySet_sep r hrs p hps hpr
    rw [hpx, hry] at this
    exact this
  -- the window
  have hwin : ∀ x ∈ properFareyReals Q, δ / 2 ≤ x ∧ x + δ / 2 ≤ 1 := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hunpack x hx
    obtain ⟨hpf, hlt⟩ := mem_properFareySet.mp hp
    obtain ⟨⟨ha1, _⟩, ⟨hq1, hqQ⟩, _, _⟩ := mem_fareySet.mp hpf
    have haR : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast ha1
    have hqR : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hq1
    have hqQR : (p.2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
    have hltR : (p.1 : ℝ) + 1 ≤ (p.2 : ℝ) := by exact_mod_cast hlt
    have hq0 : (0 : ℝ) < (p.2 : ℝ) := by linarith
    have hhalf : δ / 2 ≤ 1 / (Q : ℝ) := by
      rw [hδdef, div_div, div_le_div_iff₀ (by positivity) hQ0]
      nlinarith [hQR]
    have hinvq : (1 : ℝ) / (Q : ℝ) ≤ 1 / (p.2 : ℝ) := by
      rw [div_le_div_iff₀ hQ0 hq0]
      linarith
    constructor
    · rw [← hpx]
      have hstep : (1 : ℝ) / (p.2 : ℝ) ≤ (p.1 : ℝ) / (p.2 : ℝ) := by
        rw [div_le_div_iff₀ hq0 hq0]
        nlinarith [haR, hq0]
      linarith
    · rw [← hpx]
      have hupper : (p.1 : ℝ) / (p.2 : ℝ) ≤ 1 - 1 / (p.2 : ℝ) := by
        rw [le_sub_iff_add_le, ← add_div, div_le_one hq0]
        linarith
      linarith
  have hbase := largeSieve_gallagher_circle N hN c (properFareyReals Q) hδ hne hsep hwin
  have hinv : (1 : ℝ) / δ = (Q : ℝ) ^ (2 : ℕ) := by
    rw [hδdef, one_div_one_div]
  rw [hinv] at hbase
  exact hbase

end RHTower.Sieve
