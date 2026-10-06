import GaloisForLFunctions.RHTower.KuznetsovSameSignParseval

/-!
# The cusp `∞` of `Γ₀(Q)` inside the finite deck

For `Q ∣ N+1` let `H ≤ SL₂(ℤ)/Γ(N+1)` be the image of `Γ₀(Q)` and `1_H` its indicator vector.  Then
`ρ(T)1_H = 1_H` (`T ∈ Γ₀(Q)`), so `1_H` is a cusp vector of every integral frequency
(`isCuspEigen_gamma0Vec`), and

`⟨1_H, ρ(M)⁻¹ 1_H⟩ = |H| · [M ∈ Γ₀(Q)] = |H| · [Q ∣ c]`   (`M = (a b; c d)`)

(`inner_gamma0Vec_symm`).  Hence the same-sign row weight of the pair `(1_H, 1_H)` is
`|H| [Q ∣ c] e((μd + νa)/c)` (`rowWeightPlus_gamma0Vec`), the summand of the classical Kloosterman sum
`S(μ, ν; c)` of `Γ₀(Q)` at the cusp `∞`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

local instance gammaNormalGZ (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

variable {N : ℕ}

theorem gamma_le_gamma0_of_dvd {Q : ℕ} (hQ : Q ∣ N + 1) :
    CongruenceSubgroup.Gamma (N + 1) ≤ CongruenceSubgroup.Gamma0 Q := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  rw [CongruenceSubgroup.Gamma0_mem]
  have h1 : ((N + 1 : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by exact_mod_cast hγ.2.2.1)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ((Int.natCast_dvd_natCast.2 hQ).trans h1)

/-- The image `H` of `Γ₀(Q)` in the deck group. -/
def gamma0Deck (N Q : ℕ) : Subgroup (Deck N) :=
  (CongruenceSubgroup.Gamma0 Q).map (QuotientGroup.mk' (CongruenceSubgroup.Gamma (N + 1)))

theorem mk_mem_gamma0Deck {Q : ℕ} (hQ : Q ∣ N + 1) (M : SL(2, ℤ)) :
    (QuotientGroup.mk M : Deck N) ∈ gamma0Deck N Q ↔ M ∈ CongruenceSubgroup.Gamma0 Q := by
  constructor
  · rintro ⟨A, hA, hAM⟩
    have h : A⁻¹ * M ∈ CongruenceSubgroup.Gamma (N + 1) := QuotientGroup.eq.1 hAM
    have h' := gamma_le_gamma0_of_dvd hQ h
    have := (CongruenceSubgroup.Gamma0 Q).mul_mem hA h'
    simpa using this
  · intro hM
    exact ⟨M, hM, rfl⟩

open Classical in
/-- The indicator vector `1_H` of the image of `Γ₀(Q)`. -/
def gamma0Vec (N Q : ℕ) : DeckSpace N :=
  WithLp.toLp 2 fun q => if q ∈ gamma0Deck N Q then (1 : ℂ) else 0

open Classical in
theorem gamma0Vec_apply (Q : ℕ) (q : Deck N) :
    (gamma0Vec N Q).ofLp q = if q ∈ gamma0Deck N Q then (1 : ℂ) else 0 := rfl

theorem deckRho_apply_ofLp (M : SL(2, ℤ)) (v : DeckSpace N) (q : Deck N) :
    (deckRho N M v).ofLp q = v.ofLp (q * (QuotientGroup.mk M : Deck N)) := rfl

theorem deckRho_symm_apply_ofLp (M : SL(2, ℤ)) (v : DeckSpace N) (q : Deck N) :
    ((deckRho N M).symm v).ofLp q = v.ofLp (q * (QuotientGroup.mk M : Deck N)⁻¹) := by
  rw [← deckRho_inv, deckRho_apply_ofLp, QuotientGroup.mk_inv]

/-- **`ρ(T) 1_H = 1_H`.** -/
theorem deckRho_T_gamma0Vec {Q : ℕ} (hQ : Q ∣ N + 1) :
    deckRho N ModularGroup.T (gamma0Vec N Q) = gamma0Vec N Q := by
  have hT : (QuotientGroup.mk ModularGroup.T : Deck N) ∈ gamma0Deck N Q := by
    rw [mk_mem_gamma0Deck hQ, CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  ext q
  rw [deckRho_apply_ofLp, gamma0Vec_apply, gamma0Vec_apply]
  congr 1
  exact propext ⟨fun h => by simpa using (gamma0Deck N Q).mul_mem h ((gamma0Deck N Q).inv_mem hT),
    fun h => (gamma0Deck N Q).mul_mem h hT⟩

/-- `1_H` is a cusp vector of every integral frequency. -/
theorem isCuspEigen_gamma0Vec {Q : ℕ} (hQ : Q ∣ N + 1) (m : ℤ) :
    IsCuspEigen (m : ℝ) (gamma0Vec N Q) := by
  rw [IsCuspEigen, deckRho_T_gamma0Vec hQ]
  have : cexp (2 * Real.pi * Complex.I * ((m : ℝ) : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I m
  rw [this, one_smul]

open Classical in
/-- **`⟨1_H, ρ(M)⁻¹ 1_H⟩ = |H| [M ∈ Γ₀(Q)]`.** -/
theorem inner_gamma0Vec_symm {Q : ℕ} (hQ : Q ∣ N + 1) (M : SL(2, ℤ)) :
    ⟪gamma0Vec N Q, (deckRho N M).symm (gamma0Vec N Q)⟫_ℂ =
      (Fintype.card (gamma0Deck N Q) : ℂ) * if M ∈ CongruenceSubgroup.Gamma0 Q then 1 else 0 := by
  rw [PiLp.inner_apply]
  simp only [deckRho_symm_apply_ofLp, gamma0Vec_apply, RCLike.inner_apply']
  rw [← mk_mem_gamma0Deck hQ]
  set H := gamma0Deck N Q
  set g : Deck N := QuotientGroup.mk M
  by_cases hg : g ∈ H
  · have hpt : ∀ q : Deck N, (starRingEnd ℂ) (if q ∈ H then (1 : ℂ) else 0) *
        (if q * g⁻¹ ∈ H then (1 : ℂ) else 0) = if q ∈ H then 1 else 0 := fun q => by
      by_cases hq : q ∈ H
      · have := H.mul_mem hq (H.inv_mem hg); simp [hq, this]
      · simp [hq]
    simp_rw [hpt]
    rw [if_pos hg, mul_one, Finset.sum_boole, Fintype.card_subtype]
  · have hpt : ∀ q : Deck N, (starRingEnd ℂ) (if q ∈ H then (1 : ℂ) else 0) *
        (if q * g⁻¹ ∈ H then (1 : ℂ) else 0) = 0 := fun q => by
      by_cases hq : q ∈ H
      · have : q * g⁻¹ ∉ H := fun h => hg (by
          have := H.inv_mem (H.mul_mem (H.inv_mem hq) h)
          simpa using this)
        simp [hq, this]
      · simp [hq]
    simp_rw [hpt]
    rw [if_neg hg]; simp

open Classical in
/-- **The same-sign row weight of `(1_H, 1_H)`**: `|H| [Q ∣ c] e((μd + νa)/c)`. -/
theorem rowWeightPlus_gamma0Vec {Q : ℕ} (hQ : Q ∣ N + 1) (μ ν : ℝ) (p : gammaSet 1 1 0) :
    rowWeightPlus μ ν (gamma0Vec N Q) (gamma0Vec N Q) p =
      (Fintype.card (gamma0Deck N Q) : ℂ) *
        (if ((p.1 0 : ℤ) : ZMod Q) = 0 then 1 else 0) *
        cexp (2 * Real.pi * Complex.I *
          ((μ * (p.1 1 : ℂ) + ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ))) := by
  classical
  rw [rowWeightPlus, inner_gamma0Vec_symm hQ, CongruenceSubgroup.Gamma0_mem,
    gammaSetMatrix_apply_one_zero]
  rcases _root_.em (((p.1 0 : ℤ) : ZMod Q) = 0) with h | h <;> simp [h]

open Classical in
/-- `⟨1_H, 1_H + ρ(−1)⁻¹1_H⟩ = 2|H|`. -/
theorem inner_gamma0Vec_add_neg_one {Q : ℕ} (hQ : Q ∣ N + 1) :
    ⟪gamma0Vec N Q, gamma0Vec N Q + (deckRho N (-1)).symm (gamma0Vec N Q)⟫_ℂ =
      2 * (Fintype.card (gamma0Deck N Q) : ℂ) := by
  have h1 := inner_gamma0Vec_symm hQ 1
  have h2 := inner_gamma0Vec_symm hQ (-1)
  have hm1 : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 Q := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp
  have h0 : (deckRho N 1).symm (gamma0Vec N Q) = gamma0Vec N Q := by
    ext q; rw [deckRho_symm_apply_ofLp]; simp
  rw [h0, if_pos (CongruenceSubgroup.Gamma0 Q).one_mem, mul_one] at h1
  rw [inner_add_right, h2, if_pos hm1, h1]
  ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
