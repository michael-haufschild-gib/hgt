import GaloisForLFunctions.RHTower.XiShiftedHardEdgeDensityMeasure

/-!
# The divided-jet Gram law of the hard-edge form and its parity companion

A squared-variable state with a root of multiplicity `m` at `r` is `(u - r)^m·G` with `G` regular
there, and its divided descendants are the division-free expressions `(u - r)^(m-k)·G`.  Every
pairing of two descendants against the literal hard-edge density is therefore one member of the
moment sequence

`N k = ⟨(u - r)^k·G², η_σ⟩`,

indexed by the sum of the two divided orders.  Two facts follow with no further analysis:

* the even Gram entry of the `p`-th and `q`-th descendants is `N ((m-p) + (m-q))`;
* the odd Gram entry — the same pair multiplied by the Fourier variable — is
  `N ((m-p) + (m-q) + 1) + r·N ((m-p) + (m-q))`.

In the terminal corner `p = q = m` the first summand is the moment one step above the terminal one,
so whenever that vanishes the odd terminal energy is exactly `r` times the even terminal mass.
The vanishing itself is the semidefinite Hankel bootstrap applied to the moment sequence.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The `k`-th divided-jet moment of the state `(u - r)^m·G` at the root `r`. -/
def routeUJetMoment (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (k : ℕ) : ℝ :=
  routeUHardEdgePairing σ fun u => (u - r) ^ k * G u ^ 2

/-- The `k`-th divided descendant of the state `(u - r)^m·G`, written without division. -/
def routeUJetDescendant (m : ℕ) (r : ℝ) (G : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun u => (u - r) ^ (m - k) * G u

/-! ## The even Gram entries -/

theorem routeUEvenForm_descendant (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m p q : ℕ) :
    routeUHardEdgeEvenForm σ (routeUJetDescendant m r G p) (routeUJetDescendant m r G q)
      = routeUJetMoment σ G r ((m - p) + (m - q)) := by
  rw [routeUHardEdgeEvenForm, routeUJetMoment]
  congr 1
  funext u
  rw [routeUJetDescendant, routeUJetDescendant, pow_add]
  ring

/-! ## The odd Gram entries -/

/-- **(HPJI.6) The odd Gram entry of two divided descendants.** -/
theorem routeUOddForm_descendant (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m p q : ℕ)
    (h1 : IntegrableOn (fun u : ℝ =>
      (u - r) ^ ((m - p) + (m - q) + 1) * G u ^ 2
        * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (h2 : IntegrableOn (fun u : ℝ =>
      r * ((u - r) ^ ((m - p) + (m - q)) * G u ^ 2)
        * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0)) :
    routeUHardEdgeOddForm σ (routeUJetDescendant m r G p) (routeUJetDescendant m r G q)
      = routeUJetMoment σ G r ((m - p) + (m - q) + 1)
        + r * routeUJetMoment σ G r ((m - p) + (m - q)) := by
  have hprod : (fun u : ℝ => u * (routeUJetDescendant m r G p u * routeUJetDescendant m r G q u))
      = fun u : ℝ => u * ((u - r) ^ ((m - p) + (m - q)) * G u ^ 2) := by
    funext u
    rw [routeUJetDescendant, routeUJetDescendant, pow_add]
    ring
  rw [routeUHardEdgeOddForm, hprod, routeUHardEdgePairing_coord_jet σ G r _ h1 h2]
  rfl

/-- **(HPJI.7) The terminal odd energy is the root times the terminal even mass.** -/
theorem routeUOddForm_terminal (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m : ℕ)
    (h1 : IntegrableOn (fun u : ℝ =>
      (u - r) ^ 1 * G u ^ 2 * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (h2 : IntegrableOn (fun u : ℝ =>
      r * ((u - r) ^ 0 * G u ^ 2) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hvanish : routeUJetMoment σ G r 1 = 0) :
    routeUHardEdgeOddForm σ (routeUJetDescendant m r G m) (routeUJetDescendant m r G m)
      = r * routeUJetMoment σ G r 0 := by
  have hmm : m - m = 0 := Nat.sub_self m
  have hidx : (m - m) + (m - m) = 0 := by omega
  have hstep := routeUOddForm_descendant σ G r m m m (by rwa [hidx]) (by rwa [hidx])
  rw [hidx] at hstep
  rw [hstep, hvanish, zero_add]

/-! ## The vanishing bootstrap -/

/-- **(RJRR.9) Every divided-jet moment below the terminal one vanishes.**  The Cauchy--Schwarz
inequality of the nonnegative form and the nullity of the state on the first `m` divided moments
propagate to all moments below the terminal one. -/
theorem routeUJetMoment_eq_zero_of_null (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m : ℕ)
    (hCS : ∀ p q : ℕ, p ≤ m → q ≤ m →
      routeUJetMoment σ G r (2 * m - (p + q)) ^ 2
        ≤ routeUJetMoment σ G r (2 * m - 2 * p) * routeUJetMoment σ G r (2 * m - 2 * q))
    (hbase : ∀ j : ℕ, 1 ≤ j → j ≤ m → routeUJetMoment σ G r (2 * m - j) = 0) :
    ∀ j : ℕ, 1 ≤ j → j < 2 * m → routeUJetMoment σ G r (2 * m - j) = 0 := by
  refine psdHankel_jet_vanishing (M := fun j => routeUJetMoment σ G r (2 * m - j)) ?_ hbase
  intro p q hp hq
  exact hCS p q hp hq


/-- **Cauchy--Schwarz for the divided-jet moment sequence.**  Nonnegativity of the even form on the
one-parameter families spanned by two descendants is exactly the Hankel Cauchy--Schwarz inequality
of the moment sequence. -/
theorem routeUJetMoment_cauchySchwarz (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m : ℕ)
    (hint : ∀ p q : ℕ, IntegrableOn (fun u : ℝ =>
      routeUJetDescendant m r G p u * routeUJetDescendant m r G q u
        * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hpsd : ∀ (p q : ℕ) (t : ℝ), 0 ≤ routeUHardEdgeEvenForm σ
      (fun u => routeUJetDescendant m r G p u + t * routeUJetDescendant m r G q u)
      (fun u => routeUJetDescendant m r G p u + t * routeUJetDescendant m r G q u)) :
    ∀ p q : ℕ, p ≤ m → q ≤ m →
      routeUJetMoment σ G r (2 * m - (p + q)) ^ 2
        ≤ routeUJetMoment σ G r (2 * m - 2 * p) * routeUJetMoment σ G r (2 * m - 2 * q) := by
  intro p q hp hq
  have hcs := routeUEvenForm_sq_le σ (routeUJetDescendant m r G p) (routeUJetDescendant m r G q)
    (hint p p) (hint p q) (hint q q) (hpsd p q)
  rw [routeUEvenForm_descendant, routeUEvenForm_descendant, routeUEvenForm_descendant] at hcs
  have h1 : (m - p) + (m - q) = 2 * m - (p + q) := by omega
  have h2 : (m - p) + (m - p) = 2 * m - 2 * p := by omega
  have h3 : (m - q) + (m - q) = 2 * m - 2 * q := by omega
  rwa [h1, h2, h3] at hcs


/-- **(RJRR.6) A null state is orthogonal to all of its own divided descendants.** -/
theorem routeUJetMoment_base_of_null (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m : ℕ)
    (hCS : ∀ p q : ℕ, p ≤ m → q ≤ m →
      routeUJetMoment σ G r (2 * m - (p + q)) ^ 2
        ≤ routeUJetMoment σ G r (2 * m - 2 * p) * routeUJetMoment σ G r (2 * m - 2 * q))
    (hnull : routeUJetMoment σ G r (2 * m) = 0) :
    ∀ j : ℕ, 1 ≤ j → j ≤ m → routeUJetMoment σ G r (2 * m - j) = 0 := by
  intro j hj1 hj2
  have h := hCS 0 j (Nat.zero_le m) hj2
  have hidx : 2 * m - 2 * 0 = 2 * m := by omega
  have hidx2 : (0 : ℕ) + j = j := by omega
  rw [hidx, hidx2, hnull, zero_mul] at h
  nlinarith [sq_nonneg (routeUJetMoment σ G r (2 * m - j))]

/-- **(HPJI.9) The complete divided-jet Gram law.**  Off the terminal corner every even Gram entry
of the divided descendants vanishes. -/
theorem routeUEvenForm_descendant_eq_zero (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m : ℕ)
    (hzero : ∀ j : ℕ, 1 ≤ j → j < 2 * m → routeUJetMoment σ G r (2 * m - j) = 0)
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpm : p ≤ m) (hqm : q ≤ m)
    (hne : ¬(p = m ∧ q = m)) :
    routeUHardEdgeEvenForm σ (routeUJetDescendant m r G p) (routeUJetDescendant m r G q) = 0 := by
  have hidx : (m - p) + (m - q) = 2 * m - (p + q) := by omega
  have hlt : p + q < 2 * m := by
    rcases Nat.lt_or_ge p m with h | h
    · omega
    · have hpm' : p = m := le_antisymm hpm h
      have hqm' : q < m := by
        rcases Nat.lt_or_ge q m with h' | h'
        · exact h'
        · exact absurd ⟨hpm', le_antisymm hqm h'⟩ hne
      omega
  rw [routeUEvenForm_descendant, hidx]
  exact hzero (p + q) (by omega) hlt

/-- **(RJRR.10)/(HPJI.9) The divided-jet Gram law of a null state.**  Given Cauchy--Schwarz for the
moment sequence and nullity of the state, every even Gram entry off the terminal corner vanishes,
and the terminal odd energy is `r` times the terminal even mass. -/
theorem routeUJetGram_of_null (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m : ℕ)
    (hCS : ∀ p q : ℕ, p ≤ m → q ≤ m →
      routeUJetMoment σ G r (2 * m - (p + q)) ^ 2
        ≤ routeUJetMoment σ G r (2 * m - 2 * p) * routeUJetMoment σ G r (2 * m - 2 * q))
    (hnull : routeUJetMoment σ G r (2 * m) = 0)
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpm : p ≤ m) (hqm : q ≤ m)
    (hne : ¬(p = m ∧ q = m)) :
    routeUHardEdgeEvenForm σ (routeUJetDescendant m r G p) (routeUJetDescendant m r G q) = 0 :=
  routeUEvenForm_descendant_eq_zero σ G r m
    (routeUJetMoment_eq_zero_of_null σ G r m hCS
      (routeUJetMoment_base_of_null σ G r m hCS hnull)) p q hp hq hpm hqm hne



/-! ## The odd twins of the nonterminal descendants -/

/-- The coordinate acts on the divided descendants as `u·F_{r,k} = r·F_{r,k} + F_{r,k-1}`. -/
theorem coord_mul_routeUJetDescendant (m : ℕ) (r : ℝ) (G : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hkm : k ≤ m) (u : ℝ) :
    u * routeUJetDescendant m r G k u
      = r * routeUJetDescendant m r G k u + routeUJetDescendant m r G (k - 1) u := by
  rw [routeUJetDescendant, routeUJetDescendant]
  have h : m - (k - 1) = (m - k) + 1 := by omega
  rw [h, pow_succ]
  ring

/-- **(HPJI.10) The odd twin of a radical descendant is again zero-energy.**  Multiplication by the
coordinate lands in the span of the descendant and its predecessor, both of which annihilate the
even form. -/
theorem routeUOddForm_of_radical (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m k : ℕ) (K : ℝ → ℝ)
    (hk : 1 ≤ k) (hkm : k ≤ m)
    (hrad : routeUHardEdgeEvenForm σ (routeUJetDescendant m r G k) K = 0)
    (hrad' : routeUHardEdgeEvenForm σ (routeUJetDescendant m r G (k - 1)) K = 0)
    (h1 : IntegrableOn (fun u : ℝ =>
      r * (routeUJetDescendant m r G k u * K u)
        * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (h2 : IntegrableOn (fun u : ℝ =>
      routeUJetDescendant m r G (k - 1) u * K u
        * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0)) :
    routeUHardEdgeOddForm σ (routeUJetDescendant m r G k) K = 0 := by
  have hsplit : (fun u : ℝ => u * (routeUJetDescendant m r G k u * K u))
      = fun u : ℝ => r * (routeUJetDescendant m r G k u * K u)
        + routeUJetDescendant m r G (k - 1) u * K u := by
    funext u
    have h := coord_mul_routeUJetDescendant m r G k hk hkm u
    calc u * (routeUJetDescendant m r G k u * K u)
        = (u * routeUJetDescendant m r G k u) * K u := by ring
      _ = (r * routeUJetDescendant m r G k u + routeUJetDescendant m r G (k - 1) u) * K u := by
          rw [h]
      _ = r * (routeUJetDescendant m r G k u * K u)
            + routeUJetDescendant m r G (k - 1) u * K u := by ring
  rw [routeUHardEdgeOddForm, hsplit, routeUHardEdgePairing_add σ _ _ h1 h2,
    routeUHardEdgePairing_const_mul σ r fun u => routeUJetDescendant m r G k u * K u]
  rw [← routeUHardEdgeEvenForm, ← routeUHardEdgeEvenForm, hrad, hrad']
  ring


/-! ## Radical membership of the nonterminal descendants -/

/-- A vector with zero diagonal energy annihilates the even form. -/
theorem routeUEvenForm_eq_zero_of_diag (σ : ℝ) (H K : ℝ → ℝ)
    (hHH : IntegrableOn
      (fun u : ℝ => H u * H u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hHK : IntegrableOn
      (fun u : ℝ => H u * K u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hKK : IntegrableOn
      (fun u : ℝ => K u * K u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hpsd : ∀ t : ℝ,
      0 ≤ routeUHardEdgeEvenForm σ (fun u => H u + t * K u) (fun u => H u + t * K u))
    (hdiag : routeUHardEdgeEvenForm σ H H = 0) :
    routeUHardEdgeEvenForm σ H K = 0 := by
  have h := routeUEvenForm_sq_le σ H K hHH hHK hKK hpsd
  rw [hdiag, zero_mul] at h
  nlinarith [sq_nonneg (routeUHardEdgeEvenForm σ H K)]

/-- **(RJRR.8) The nonterminal divided descendants have zero diagonal energy.** -/
theorem routeUJetDescendant_diag_eq_zero (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (m k : ℕ)
    (hk : 1 ≤ k) (hkm : k < m)
    (hzero : ∀ j : ℕ, 1 ≤ j → j < 2 * m → routeUJetMoment σ G r (2 * m - j) = 0) :
    routeUHardEdgeEvenForm σ (routeUJetDescendant m r G k) (routeUJetDescendant m r G k) = 0 := by
  rw [routeUEvenForm_descendant]
  have hidx : (m - k) + (m - k) = 2 * m - 2 * k := by omega
  rw [hidx]
  exact hzero (2 * k) (by omega) (by omega)

/-! ## Independence of the divided principal parts -/

/-- **The divided descendants of a nonzero state are linearly independent.**  Their rational
principal parts are distinct powers of `u - r`, so a vanishing combination forces a polynomial with
infinitely many roots. -/
theorem routeUJetDescendant_eq_zero_of_sum_eq_zero (r : ℝ) (G : ℝ → ℝ) (m : ℕ)
    {S : Set ℝ} (hS : S.Infinite) (hG : ∀ u ∈ S, G u ≠ 0) (c : ℕ → ℝ)
    (T : Finset ℕ) (hT : ∀ k ∈ T, k ≤ m)
    (hsum : ∀ u : ℝ, ∑ k ∈ T, c k * routeUJetDescendant m r G k u = 0) :
    ∀ k ∈ T, c k = 0 := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℝ,
      P = ∑ k ∈ T, Polynomial.C (c k) * Polynomial.X ^ (m - k) := ⟨_, rfl⟩
  have heval : ∀ u ∈ S, P.eval (u - r) = 0 := by
    intro u hu
    have hGu : G u ≠ 0 := hG u hu
    have h := hsum u
    have hexp : ∑ k ∈ T, c k * routeUJetDescendant m r G k u
        = (∑ k ∈ T, c k * (u - r) ^ (m - k)) * G u := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [routeUJetDescendant]
      ring
    rw [hexp, mul_eq_zero] at h
    have hpoly : ∑ k ∈ T, c k * (u - r) ^ (m - k) = 0 := h.resolve_right hGu
    rw [hP, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hpoly
  have hsub : (fun u : ℝ => u - r) '' S ⊆ {x : ℝ | P.IsRoot x} := by
    rintro x ⟨u, hu, rfl⟩
    exact heval u hu
  have hinj : Set.InjOn (fun u : ℝ => u - r) S := fun a _ b _ hab => by
    simpa using sub_left_injective hab
  have himg : ((fun u : ℝ => u - r) '' S).Infinite := hS.image hinj
  have hroots : {x : ℝ | P.IsRoot x}.Infinite := himg.mono hsub
  have hzero : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hroots
  intro k hk
  have hkm : k ≤ m := hT k hk
  have hcoeff : P.coeff (m - k) = c k := by
    rw [hP, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single k]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    · intro j hj hjk
      have hjm : j ≤ m := hT j hj
      have hne : ¬ (m - k = m - j) := by omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
    · intro hknot
      exact absurd hk hknot
  rw [← hcoeff, hzero, Polynomial.coeff_zero]

end RHTower

end
