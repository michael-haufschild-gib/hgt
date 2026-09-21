import GaloisForLFunctions.RHTower.RouteEComponentHistoryGibbsParity

/-!
# Route E complete replica-cell coprimality no-go

A full opposite-parity row on a complete replica histogram cell cannot at the same time be a
literal coprime entropy-complement relation when one prime is present and another component varies.
The result leaves sparse coprime-compatible subrelations and the endpoint ANOVA inequality open.
-/

open Finset
open scoped BigOperators

namespace RHTower

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]

def routeEPrimeComponentReceiver (p : C → ℕ) (a : C → Bool) : ℕ :=
  ∏ c, if a c then p c else 1

def routeEAnchorParity (a : C → Bool) : ℝ :=
  ∏ c, routeEBinaryPresenceCharacter (a c)

private theorem exists_componentHistogram_anchor
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (a : C → Bool) (hpos : ∀ c, 0 < k c (a c)) :
    ∃ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k, x 0 = a := by
  classical
  let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
  have hratio := routeE_componentHistogram_anchor_zero_joint_ratio
    (fun _ : C => Bool) m k a hk
  have hright : 0 < ∏ c, (k c (a c) : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro c _hc
    exact div_pos (by exact_mod_cast hpos c) (by positivity)
  rw [← hratio] at hright
  have hnonempty : (cell.filter fun x => x 0 = a).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    rw [hempty] at hright
    simp at hright
  obtain ⟨x, hx⟩ := hnonempty
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

omit [DecidableEq C] in
private theorem routeEPrimeComponentReceiver_dvd
    (p : C → ℕ) (a : C → Bool) (c : C) (hc : a c = true) :
    p c ∣ routeEPrimeComponentReceiver p a := by
  unfold routeEPrimeComponentReceiver
  have h := Finset.dvd_prod_of_mem (fun e => if a e then p e else 1) (Finset.mem_univ c)
  simpa [hc] using h

private theorem routeEAnchorParity_toggle
    (a b : C → Bool) (d : C)
    (hrest : ∀ e, e ≠ d → a e = b e)
    (ha : a d = true) (hb : b d = false) :
    routeEAnchorParity a = - routeEAnchorParity b := by
  classical
  unfold routeEAnchorParity
  rw [show (∏ e, routeEBinaryPresenceCharacter (a e)) =
      routeEBinaryPresenceCharacter (a d) *
        ∏ e ∈ (Finset.univ.erase d), routeEBinaryPresenceCharacter (a e) by
      symm
      exact Finset.mul_prod_erase Finset.univ
        (fun e => routeEBinaryPresenceCharacter (a e)) (Finset.mem_univ d),
    show (∏ e, routeEBinaryPresenceCharacter (b e)) =
      routeEBinaryPresenceCharacter (b d) *
        ∏ e ∈ (Finset.univ.erase d), routeEBinaryPresenceCharacter (b e) by
      symm
      exact Finset.mul_prod_erase Finset.univ
        (fun e => routeEBinaryPresenceCharacter (b e)) (Finset.mem_univ d)]
  have herase :
      (∏ e ∈ (Finset.univ.erase d), routeEBinaryPresenceCharacter (a e)) =
        ∏ e ∈ (Finset.univ.erase d), routeEBinaryPresenceCharacter (b e) := by
    apply Finset.prod_congr rfl
    intro e he
    have hed : e ≠ d := by
      exact (Finset.mem_erase.mp he).1
    rw [hrest e hed]
  rw [herase, ha, hb]
  norm_num [routeEBinaryPresenceCharacter]

theorem routeE_two_variable_histogram_complete_coprime_noGo
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (p : C → ℕ) (hp : ∀ c, Nat.Prime (p c))
    (c d : C) (hcd : c ≠ d)
    (hcT : 0 < k c true)
    (hdT : 0 < k d true) (hdF : 0 < k d false) :
    ¬ (∀ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
        ∀ y ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
          routeEAnchorParity (x 0) = -routeEAnchorParity (y 0) →
            Nat.Coprime (routeEPrimeComponentReceiver p (x 0))
              (routeEPrimeComponentReceiver p (y 0))) := by
  classical
  let a : C → Bool := fun e =>
    if e = c then true else if e = d then true else
      if 0 < k e true then true else false
  let b : C → Bool := fun e =>
    if e = c then true else if e = d then false else
      if 0 < k e true then true else false
  have hapos : ∀ e, 0 < k e (a e) := by
    intro e
    dsimp [a]
    split_ifs with hec hed htrue
    · simpa [hec] using hcT
    · simpa [hed] using hdT
    · exact htrue
    · have hsum : k e true + k e false = m + 1 := by
        simpa [Fintype.sum_bool] using hk e
      omega
  have hbpos : ∀ e, 0 < k e (b e) := by
    intro e
    dsimp [b]
    split_ifs with hec hed htrue
    · simpa [hec] using hcT
    · simpa [hed] using hdF
    · exact htrue
    · have hsum : k e true + k e false = m + 1 := by
        simpa [Fintype.sum_bool] using hk e
      omega
  obtain ⟨x, hx, hx0⟩ := exists_componentHistogram_anchor m k hk a hapos
  obtain ⟨y, hy, hy0⟩ := exists_componentHistogram_anchor m k hk b hbpos
  intro hcomplete
  have hac : a c = true := by simp [a]
  have hbc : b c = true := by simp [b]
  have had : a d = true := by simp [a]
  have hdc : d ≠ c := Ne.symm hcd
  have hbd : b d = false := by simp [b, hdc]
  have habrest : ∀ e, e ≠ d → a e = b e := by
    intro e hed
    dsimp [a, b]
    by_cases hec : e = c
    · simp [hec]
    · simp [hec, hed]
  have hparity : routeEAnchorParity (x 0) = -routeEAnchorParity (y 0) := by
    rw [hx0, hy0]
    exact routeEAnchorParity_toggle a b d habrest had hbd
  have hcop := hcomplete x hx y hy hparity
  have hdivx : p c ∣ routeEPrimeComponentReceiver p (x 0) := by
    rw [hx0]
    exact routeEPrimeComponentReceiver_dvd p a c hac
  have hdivy : p c ∣ routeEPrimeComponentReceiver p (y 0) := by
    rw [hy0]
    exact routeEPrimeComponentReceiver_dvd p b c hbc
  have hgcd : p c ∣ Nat.gcd (routeEPrimeComponentReceiver p (x 0))
      (routeEPrimeComponentReceiver p (y 0)) := Nat.dvd_gcd hdivx hdivy
  have hone : Nat.gcd (routeEPrimeComponentReceiver p (x 0))
      (routeEPrimeComponentReceiver p (y 0)) = 1 := hcop.gcd_eq_one
  have hpone : p c = 1 := Nat.dvd_one.mp (by simpa [hone] using hgcd)
  exact (hp c).ne_one hpone

/-- A complete coprime opposite-parity row is rigid: once a distinct prime component occurs,
every other component has deterministic anchor occupancy.  Hence a mixed complete row has at most
one varying prime component. -/
theorem routeE_completeCoprimeParityRows_component_rigidity
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (p : C → ℕ) (hp : ∀ c, Nat.Prime (p c))
    (c d : C) (hcd : c ≠ d)
    (hcT : 0 < k c true)
    (hcomplete :
      ∀ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
        ∀ y ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
          routeEAnchorParity (x 0) = -routeEAnchorParity (y 0) →
            Nat.Coprime (routeEPrimeComponentReceiver p (x 0))
              (routeEPrimeComponentReceiver p (y 0))) :
    k d true = 0 ∨ k d false = 0 := by
  by_contra hdet
  push Not at hdet
  exact (routeE_two_variable_histogram_complete_coprime_noGo
    m k hk p hp c d hcd hcT
    (Nat.pos_of_ne_zero hdet.1) (Nat.pos_of_ne_zero hdet.2)) hcomplete

end

end RHTower
