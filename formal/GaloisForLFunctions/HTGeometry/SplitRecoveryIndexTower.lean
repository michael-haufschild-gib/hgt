import GaloisForLFunctions.HTGeometry.FormationCloneRigidityCompletion

/-!
# Finite split-recovery index reconstruction

A strictly positive finite split recovery is a conditional expectation with an explicit Watatani
quasi-basis.  Its full index profile is the pointwise reciprocal of the recovery kernel, so profile
and kernel determine each other, and a positive profile is realizable exactly when its reciprocals
form probability rows.  The least Pimsner--Popa constant is the largest reciprocal weight, it is
bounded below by the latent cardinality with equality only at the uniform kernel, and it composes
multiplicatively under iterated formation, so a uniformly bounded recovery tower forces trivial
latent formation.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {X H : Type*} [Fintype X] [Fintype H] [DecidableEq H]

/-- A strictly positive finite split recovery kernel. -/
structure SplitRecovery (X H : Type*) [Fintype H] where
  /-- The recovery weights. -/
  kernel : X → H → ℝ
  /-- Strict positivity. -/
  pos : ∀ x h, 0 < kernel x h
  /-- Row normalization. -/
  row : ∀ x, ∑ h, kernel x h = 1

namespace SplitRecovery

variable (κ : SplitRecovery X H)

/-- The conditional expectation attached to the recovery. -/
def expect (f : X × H → ℝ) (x : X) : ℝ := ∑ h, κ.kernel x h * f (x, h)

/-- The Watatani quasi-basis element at latent index `h`. -/
def qbasis (h : H) (p : X × H) : ℝ :=
  if h = p.2 then 1 / Real.sqrt (κ.kernel p.1 h) else 0

@[simp] theorem qbasis_self (h : H) (x : X) :
    κ.qbasis h (x, h) = 1 / Real.sqrt (κ.kernel x h) := by
  simp [qbasis]

theorem qbasis_of_ne {h k : H} (hk : h ≠ k) (x : X) : κ.qbasis h (x, k) = 0 := by
  simp [qbasis, hk]

theorem sqrt_kernel_pos (x : X) (h : H) : 0 < Real.sqrt (κ.kernel x h) :=
  Real.sqrt_pos.2 (κ.pos x h)

theorem sqrt_kernel_mul_self (x : X) (h : H) :
    Real.sqrt (κ.kernel x h) * Real.sqrt (κ.kernel x h) = κ.kernel x h :=
  Real.mul_self_sqrt (κ.pos x h).le

/-- The conditional expectation is unital. -/
theorem expect_one (x : X) : κ.expect (fun _ => 1) x = 1 := by
  simp only [expect, mul_one]
  exact κ.row x

/-- The conditional expectation is positive. -/
theorem expect_nonneg {f : X × H → ℝ} (hf : ∀ q, 0 ≤ f q) (x : X) : 0 ≤ κ.expect f x :=
  Finset.sum_nonneg fun h _ => mul_nonneg (κ.pos x h).le (hf _)

/-- The conditional expectation is faithful. -/
theorem eq_zero_of_expect_eq_zero {f : X × H → ℝ} (hf : ∀ q, 0 ≤ f q) {x : X}
    (h : κ.expect f x = 0) (k : H) : f (x, k) = 0 := by
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun h _ => mul_nonneg (κ.pos x h).le (hf _))).1 h k (Finset.mem_univ k)
  rcases mul_eq_zero.1 hterm with hz | hz
  · exact absurd hz (κ.pos x k).ne'
  · exact hz

/-- **Quasi-basis reconstruction** (card `(RIT.6)`). -/
theorem quasiBasis (f : X × H → ℝ) (p : X × H) :
    ∑ h, κ.qbasis h p * κ.expect (fun q => κ.qbasis h q * f q) p.1 = f p := by
  obtain ⟨x, k⟩ := p
  have hinner : ∀ h : H, κ.expect (fun q => κ.qbasis h q * f q) x
      = Real.sqrt (κ.kernel x h) * f (x, h) := by
    intro h
    have hterm : ∀ j : H, κ.kernel x j * (κ.qbasis h (x, j) * f (x, j))
        = if j = h then Real.sqrt (κ.kernel x h) * f (x, h) else 0 := by
      intro j
      by_cases hj : j = h
      · subst hj
        rw [if_pos rfl, κ.qbasis_self j x]
        have hs2 := κ.sqrt_kernel_mul_self x j
        set s := Real.sqrt (κ.kernel x j) with hsdef
        have hsne : s ≠ 0 := by
          rw [hsdef]
          exact (κ.sqrt_kernel_pos x j).ne'
        rw [← hs2]
        field_simp
      · rw [if_neg hj, κ.qbasis_of_ne (fun hc => hj hc.symm) x]
        ring
    simp only [expect]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq' Finset.univ h]
    simp
  simp only [hinner]
  have hterm : ∀ h : H, κ.qbasis h (x, k) * (Real.sqrt (κ.kernel x h) * f (x, h))
      = if h = k then f (x, k) else 0 := by
    intro h
    by_cases hh : h = k
    · subst hh
      rw [if_pos rfl, κ.qbasis_self h x]
      have hsne : Real.sqrt (κ.kernel x h) ≠ 0 := (κ.sqrt_kernel_pos x h).ne'
      field_simp
    · rw [if_neg hh, κ.qbasis_of_ne hh x]
      ring
  rw [Finset.sum_congr rfl fun h _ => hterm h, Finset.sum_ite_eq' Finset.univ k]
  simp

/-- The full Watatani index profile. -/
def index (p : X × H) : ℝ := ∑ k, (κ.qbasis k p) ^ 2

/-- **The index profile is the reciprocal kernel** (card `(RIT.7)`). -/
theorem index_eq (p : X × H) : κ.index p = 1 / κ.kernel p.1 p.2 := by
  obtain ⟨x, h⟩ := p
  have hterm : ∀ k : H, (κ.qbasis k (x, h)) ^ 2 = if k = h then 1 / κ.kernel x h else 0 := by
    intro k
    by_cases hk : k = h
    · subst hk
      rw [if_pos rfl, κ.qbasis_self k x, div_pow, one_pow, Real.sq_sqrt (κ.pos x k).le]
    · rw [if_neg hk, κ.qbasis_of_ne hk x]
      norm_num
  rw [index, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq' Finset.univ h]
  simp

theorem index_pos (p : X × H) : 0 < κ.index p := by
  rw [index_eq]
  exact div_pos one_pos (κ.pos p.1 p.2)

/-- **The index profile reconstructs the kernel** (card `(RIT.8)`). -/
theorem kernel_eq_index_inv (x : X) (h : H) : κ.kernel x h = (κ.index (x, h))⁻¹ := by
  rw [index_eq]
  simp

/-- **Realizability of an index profile** (card `(RIT.9)`). -/
theorem exists_index_eq (J : X → H → ℝ) (hJ : ∀ x h, 0 < J x h)
    (hrow : ∀ x, ∑ h, (J x h)⁻¹ = 1) :
    ∃ κ : SplitRecovery X H, ∀ x h, κ.index (x, h) = J x h := by
  refine ⟨⟨fun x h => (J x h)⁻¹, fun x h => inv_pos.2 (hJ x h), hrow⟩, fun x h => ?_⟩
  rw [index_eq]
  simp only
  rw [one_div, inv_inv]

/-! ## The exact Pimsner--Popa scalar -/

section PimsnerPopa

variable [Nonempty X] [Nonempty H] (κ : SplitRecovery X H)

/-- The least Pimsner--Popa constant of the recovery. -/
def pimsnerPopa : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun p : X × H => 1 / κ.kernel p.1 p.2

theorem le_pimsnerPopa (p : X × H) : 1 / κ.kernel p.1 p.2 ≤ κ.pimsnerPopa :=
  Finset.le_sup' (fun q : X × H => 1 / κ.kernel q.1 q.2) (Finset.mem_univ p)

theorem pimsnerPopa_pos : 0 < κ.pimsnerPopa := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨h⟩ := (inferInstance : Nonempty H)
  exact lt_of_lt_of_le (div_pos one_pos (κ.pos x h)) (κ.le_pimsnerPopa (x, h))

/-- **The least positivity constant** (card `(RIT.11)`). -/
theorem pimsnerPopa_least (K : ℝ) :
    (∀ f : X × H → ℝ, (∀ q, 0 ≤ f q) → ∀ p : X × H, 0 ≤ K * κ.expect f p.1 - f p)
      ↔ κ.pimsnerPopa ≤ K := by
  classical
  constructor
  · intro h
    refine Finset.sup'_le _ _ fun p _ => ?_
    obtain ⟨x, k⟩ := p
    have hpt := h (fun q => if q = (x, k) then 1 else 0) (fun q => by positivity) (x, k)
    have hexp : κ.expect (fun q => if q = (x, k) then (1 : ℝ) else 0) x = κ.kernel x k := by
      simp only [expect]
      have hterm : ∀ j : H, κ.kernel x j * (if (x, j) = (x, k) then (1 : ℝ) else 0)
          = if j = k then κ.kernel x k else 0 := by
        intro j
        by_cases hj : j = k
        · subst hj; simp
        · rw [if_neg (by simpa using hj), if_neg hj, mul_zero]
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq' Finset.univ k]
      simp
    rw [hexp, if_pos rfl] at hpt
    rw [div_le_iff₀ (κ.pos x k)]
    linarith
  · intro hK f hf p
    obtain ⟨x, k⟩ := p
    have hKpos : 0 < K := lt_of_lt_of_le κ.pimsnerPopa_pos hK
    have hkey : 1 / κ.kernel x k ≤ K := le_trans (κ.le_pimsnerPopa (x, k)) hK
    have hone : 1 ≤ K * κ.kernel x k := by
      rw [div_le_iff₀ (κ.pos x k)] at hkey
      linarith
    have hsplit : κ.kernel x k * f (x, k) ≤ κ.expect f x := by
      simp only [expect]
      refine Finset.single_le_sum (f := fun j => κ.kernel x j * f (x, j)) ?_ (Finset.mem_univ k)
      intro j _
      exact mul_nonneg (κ.pos x j).le (hf _)
    have hmul : K * (κ.kernel x k * f (x, k)) ≤ K * κ.expect f x :=
      mul_le_mul_of_nonneg_left hsplit hKpos.le
    nlinarith [hf (x, k), hone, hmul]

/-- **The latent cardinality is a lower bound** (card `(RIT.12)`). -/
theorem card_le_pimsnerPopa : (Fintype.card H : ℝ) ≤ κ.pimsnerPopa := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsum : ∑ h : H, κ.kernel x h ≤ ∑ _h : H, (1 : ℝ) / (Fintype.card H : ℝ) := by
    rw [κ.row x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div,
      div_self hcard.ne']
  obtain ⟨h, -, hh⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine le_trans ?_ (κ.le_pimsnerPopa (x, h))
  rw [le_div_iff₀ (κ.pos x h)]
  rw [le_div_iff₀ hcard] at hh
  linarith

/-- **Equality holds exactly at the uniform kernel.** -/
theorem pimsnerPopa_eq_card_iff :
    κ.pimsnerPopa = (Fintype.card H : ℝ) ↔ ∀ x h, κ.kernel x h = 1 / (Fintype.card H : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · intro heq x
    have hge : ∀ h : H, 1 / (Fintype.card H : ℝ) ≤ κ.kernel x h := by
      intro h
      have := κ.le_pimsnerPopa (x, h)
      rw [heq] at this
      rw [div_le_iff₀ hcard]
      rw [div_le_iff₀ (κ.pos x h)] at this
      linarith
    intro h
    by_contra hne
    have hlt : 1 / (Fintype.card H : ℝ) < κ.kernel x h := lt_of_le_of_ne (hge h) (Ne.symm hne)
    have hsum : ∑ _k : H, (1 : ℝ) / (Fintype.card H : ℝ) < ∑ k : H, κ.kernel x k :=
      Finset.sum_lt_sum (fun k _ => hge k) ⟨h, Finset.mem_univ h, hlt⟩
    rw [κ.row x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div,
      div_self hcard.ne'] at hsum
    exact lt_irrefl 1 hsum
  · intro huni
    refine le_antisymm (Finset.sup'_le _ _ fun p _ => ?_) (κ.card_le_pimsnerPopa)
    rw [huni p.1 p.2, one_div_one_div]

end PimsnerPopa

end SplitRecovery


/-! ## The Rényi equation of state -/

section Renyi

variable {H : Type*} [Fintype H] [Nonempty H]

/-- Finite Rényi divergence from a reference law. -/
def finiteRenyiDiv (p u : H → ℝ) (alpha : ℝ) : ℝ :=
  Real.log (∑ h, p h ^ alpha * u h ^ (1 - alpha)) / (alpha - 1)

/-- **Index moment form of the Rényi entropy** (card `(RIT.16)`). -/
theorem finiteRenyiEntropy_eq_index_moment (q : H → ℝ) (hq : ∀ h, 0 < q h) (alpha : ℝ) :
    finiteRenyiEntropy q alpha
      = Real.log (∑ h, q h * ((q h)⁻¹) ^ (1 - alpha)) / (1 - alpha) := by
  rw [finiteRenyiEntropy]
  congr 2
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Real.inv_rpow (hq h).le, ← Real.rpow_neg (hq h).le]
  have hadd := Real.rpow_add (hq h) 1 (-(1 - alpha))
  rw [Real.rpow_one] at hadd
  rw [← hadd]
  congr 1
  ring

/-- **Index/Rényi conservation** (card `(RIT.17)`). -/
theorem finiteRenyiDiv_add_finiteRenyiEntropy (q : H → ℝ) (hq : ∀ h, 0 < q h) (alpha : ℝ)
    (halpha : alpha ≠ 1) :
    finiteRenyiDiv q (fun _ => 1 / (Fintype.card H : ℝ)) alpha + finiteRenyiEntropy q alpha
      = Real.log (Fintype.card H : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hS : 0 < ∑ h, q h ^ alpha :=
    Finset.sum_pos (fun h _ => Real.rpow_pos_of_pos (hq h) _) Finset.univ_nonempty
  have hpow : ((1 : ℝ) / (Fintype.card H : ℝ)) ^ (1 - alpha)
      = (Fintype.card H : ℝ) ^ (alpha - 1) := by
    rw [one_div, Real.inv_rpow hcard.le, ← Real.rpow_neg hcard.le]
    congr 1
    ring
  have hsum : ∑ h, q h ^ alpha * ((1 : ℝ) / (Fintype.card H : ℝ)) ^ (1 - alpha)
      = (Fintype.card H : ℝ) ^ (alpha - 1) * ∑ h, q h ^ alpha := by
    rw [← Finset.sum_mul, hpow]
    ring
  have hane : alpha - 1 ≠ 0 := sub_ne_zero.2 halpha
  rw [finiteRenyiDiv, hsum, Real.log_mul (Real.rpow_pos_of_pos hcard _).ne' hS.ne',
    Real.log_rpow hcard, finiteRenyiEntropy]
  field_simp
  ring

/-- **Shannon-order index conservation** (card `(RIT.18)`). -/
theorem shannon_index_conservation (q : H → ℝ) (hq : ∀ h, 0 < q h) (hsum : ∑ h, q h = 1) :
    (∑ h, q h * Real.log (q h / (1 / (Fintype.card H : ℝ))))
      + ∑ h, q h * Real.log ((q h)⁻¹) = Real.log (Fintype.card H : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hleft : ∀ h : H, q h * Real.log (q h / (1 / (Fintype.card H : ℝ)))
      = q h * Real.log (Fintype.card H : ℝ) + q h * Real.log (q h) := by
    intro h
    rw [div_div_eq_mul_div, div_one, mul_comm (q h) ((Fintype.card H : ℝ)),
      Real.log_mul hcard.ne' (hq h).ne']
    ring
  have hright : ∀ h : H, q h * Real.log ((q h)⁻¹) = -(q h * Real.log (q h)) := by
    intro h
    rw [Real.log_inv]
    ring
  rw [Finset.sum_congr rfl fun h _ => hleft h, Finset.sum_congr rfl fun h _ => hright h,
    Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, Finset.sum_neg_distrib]
  ring

end Renyi

/-! ## Iterated formation and the strict tensor law -/

section Depth

variable {X H : Type*} [Fintype X] [Fintype H] [DecidableEq H]

/-- The depth-`n` iterated recovery. -/
def SplitRecovery.depth (κ : SplitRecovery X H) (n : ℕ) : SplitRecovery X (Fin n → H) where
  kernel x hs := ∏ j, κ.kernel x (hs j)
  pos x hs := Finset.prod_pos fun j _ => κ.pos x (hs j)
  row x := by
    classical
    rw [← Fintype.prod_sum fun (_ : Fin n) (h : H) => κ.kernel x h]
    simp [κ.row x]

@[simp] theorem SplitRecovery.depth_kernel (κ : SplitRecovery X H) (n : ℕ) (x : X)
    (hs : Fin n → H) : (κ.depth n).kernel x hs = ∏ j, κ.kernel x (hs j) := rfl

/-- **The depth index profile is the product profile** (card `(RIT.20)`). -/
theorem SplitRecovery.depth_index (κ : SplitRecovery X H) (n : ℕ) (x : X) (hs : Fin n → H) :
    (κ.depth n).index (x, hs) = ∏ j, (κ.kernel x (hs j))⁻¹ := by
  rw [SplitRecovery.index_eq]
  simp only [SplitRecovery.depth_kernel]
  rw [one_div, ← Finset.prod_inv_distrib]

/-- **The strict tensor law for the Pimsner--Popa scalar** (card `(RIT.21)`). -/
theorem SplitRecovery.pimsnerPopa_depth [Nonempty X] [Nonempty H] (κ : SplitRecovery X H)
    (n : ℕ) : (κ.depth n).pimsnerPopa = κ.pimsnerPopa ^ n := by
  classical
  have hKpos := κ.pimsnerPopa_pos
  refine le_antisymm (Finset.sup'_le _ _ fun p _ => ?_) ?_
  · obtain ⟨x, hs⟩ := p
    have hle : ∀ j : Fin n, 1 / κ.kernel x (hs j) ≤ κ.pimsnerPopa := fun j =>
      κ.le_pimsnerPopa (x, hs j)
    have hnn : ∀ j : Fin n, (0 : ℝ) ≤ 1 / κ.kernel x (hs j) := fun j =>
      (div_pos one_pos (κ.pos x (hs j))).le
    calc 1 / (κ.depth n).kernel x hs = ∏ j, 1 / κ.kernel x (hs j) := by
          simp only [SplitRecovery.depth_kernel]
          rw [one_div, ← Finset.prod_inv_distrib]
          exact Finset.prod_congr rfl fun j _ => (one_div _).symm
      _ ≤ ∏ _j : Fin n, κ.pimsnerPopa :=
          Finset.prod_le_prod (fun j _ => hnn j) (fun j _ => hle j)
      _ = κ.pimsnerPopa ^ n := by simp
  · obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := X × H))
      (fun q : X × H => 1 / κ.kernel q.1 q.2)
    obtain ⟨x₀, h₀⟩ := p
    have hval : 1 / (κ.depth n).kernel x₀ (fun _ => h₀) = κ.pimsnerPopa ^ n := by
      simp only [SplitRecovery.depth_kernel, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [one_div, ← inv_pow, ← one_div]
      have hpp : κ.pimsnerPopa = 1 / κ.kernel x₀ h₀ := hp
      rw [hpp]
    rw [← hval]
    exact (κ.depth n).le_pimsnerPopa (x₀, fun _ => h₀)

/-- **No nontrivial uniformly bounded recovery tower** (card `(RIT.28)`, `(RIT.29)`). -/
theorem SplitRecovery.card_pow_le_pimsnerPopa_depth [Nonempty X] [Nonempty H]
    (κ : SplitRecovery X H) (n : ℕ) :
    ((Fintype.card H : ℝ)) ^ n ≤ (κ.depth n).pimsnerPopa := by
  rw [κ.pimsnerPopa_depth n]
  exact pow_le_pow_left₀ (by positivity) κ.card_le_pimsnerPopa n

theorem SplitRecovery.bddAbove_pimsnerPopa_depth_iff [Nonempty X] [Nonempty H]
    (κ : SplitRecovery X H) :
    (∃ C : ℝ, ∀ n : ℕ, (κ.depth n).pimsnerPopa ≤ C) ↔ Fintype.card H = 1 := by
  have hcard1 : 1 ≤ Fintype.card H := Fintype.card_pos
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    have hgt : (1 : ℝ) < (Fintype.card H : ℝ) := by
      have : 2 ≤ Fintype.card H := by omega
      exact_mod_cast this
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hgt
    exact absurd (le_trans (κ.card_pow_le_pimsnerPopa_depth n) (hC n)) (not_le.2 hn)
  · intro hone
    refine ⟨1, fun n => ?_⟩
    have huni : ∀ (x : X) (h : H), κ.kernel x h = 1 := by
      intro x h
      have := κ.row x
      rw [Finset.sum_eq_single h] at this
      · exact this
      · intro b _ hb
        exact absurd (Fintype.card_le_one_iff.1 (le_of_eq hone) b h) hb
      · intro hmem
        exact absurd (Finset.mem_univ h) hmem
    have hK : κ.pimsnerPopa = 1 := by
      refine le_antisymm (Finset.sup'_le _ _ fun p _ => ?_) ?_
      · rw [huni p.1 p.2]
        norm_num
      · obtain ⟨x⟩ := (inferInstance : Nonempty X)
        obtain ⟨h⟩ := (inferInstance : Nonempty H)
        have := κ.le_pimsnerPopa (x, h)
        rw [huni x h] at this
        simpa using this
    rw [κ.pimsnerPopa_depth n, hK, one_pow]

end Depth

/-! ## The global formation equation of state -/

section EquationOfState

variable {X H : Type*} [Fintype X] [Fintype H] [DecidableEq H]

theorem sum_prod_eq_one {n : ℕ} (w : H → ℝ) (hw : ∑ h, w h = 1) :
    ∑ hs : Fin n → H, ∏ j, w (hs j) = 1 := by
  classical
  rw [← Fintype.prod_sum fun (_ : Fin n) (h : H) => w h]
  simp [hw]

/-- The exact first-order expansion of an iterated product weight. -/
theorem sum_prod_mul_sum {n : ℕ} (w : H → ℝ) (hw : ∑ h, w h = 1) (g : H → ℝ) :
    ∑ hs : Fin n → H, (∏ j, w (hs j)) * (∑ j, g (hs j)) = n * ∑ h, w h * g h := by
  classical
  have hswap : ∑ hs : Fin n → H, (∏ j, w (hs j)) * (∑ j, g (hs j))
      = ∑ j : Fin n, ∑ hs : Fin n → H, (∏ i, w (hs i)) * g (hs j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun hs _ => by rw [Finset.mul_sum]
  have hone : ∀ j : Fin n, ∑ hs : Fin n → H, (∏ i, w (hs i)) * g (hs j) = ∑ h, w h * g h := by
    intro j
    have hterm : ∀ hs : Fin n → H, (∏ i, w (hs i)) * g (hs j)
        = ∏ i, (if i = j then w (hs i) * g (hs i) else w (hs i)) := by
      intro hs
      rw [← Finset.mul_prod_erase Finset.univ (fun i => if i = j then w (hs i) * g (hs i)
        else w (hs i)) (Finset.mem_univ j), if_pos rfl,
        ← Finset.mul_prod_erase Finset.univ (fun i => w (hs i)) (Finset.mem_univ j)]
      rw [Finset.prod_congr rfl fun i hi => if_neg (Finset.ne_of_mem_erase hi)]
      ring
    rw [Finset.sum_congr rfl fun hs _ => hterm hs,
      ← Fintype.prod_sum fun (i : Fin n) (h : H) => if i = j then w h * g h else w h]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => ∑ h, if i = j then w h * g h else w h) (Finset.mem_univ j)]
    have hj : (∑ h, if j = j then w h * g h else w h) = ∑ h, w h * g h := by
      simp
    have hrest : ∀ i ∈ Finset.univ.erase j, (∑ h, if i = j then w h * g h else w h) = 1 := by
      intro i hi
      rw [Finset.sum_congr rfl fun h _ => if_neg (Finset.ne_of_mem_erase hi), hw]
    rw [hj, Finset.prod_congr rfl hrest, Finset.prod_const_one, mul_one]
  rw [hswap, Finset.sum_congr rfl fun j _ => hone j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- Discrete relative entropy of finite weight functions. -/
def finiteKL {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ := ∑ a, p a * Real.log (p a / q a)

namespace SplitRecovery

variable (κ : SplitRecovery X H)

/-- The average latent formation entropy of the recovery under an observer law. -/
def avgEntropy (μ : X → ℝ) : ℝ :=
  ∑ x, μ x * (-∑ h, κ.kernel x h * Real.log (κ.kernel x h))

/-- The formed packet at depth `n`. -/
def formedPacket (μ : X → ℝ) (n : ℕ) : X × (Fin n → H) → ℝ :=
  fun p => μ p.1 * (κ.depth n).kernel p.1 p.2

/-- The uniform latent reference packet at depth `n`. -/
def uniformPacket (μ : X → ℝ) (n : ℕ) : X × (Fin n → H) → ℝ :=
  fun p => μ p.1 * ((Fintype.card H : ℝ)⁻¹) ^ n

/-- **Latent divergence from uniform** (first summand of card `(RIT.25)`). -/
theorem finiteKL_formedPacket_uniformPacket [Nonempty H] (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hμsum : ∑ x, μ x = 1) (n : ℕ) :
    finiteKL (κ.formedPacket μ n) (uniformPacket μ n)
      = n * (Real.log (Fintype.card H : ℝ) - κ.avgEntropy μ) := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ (x : X) (hs : Fin n → H),
      κ.formedPacket μ n (x, hs) *
          Real.log (κ.formedPacket μ n (x, hs) / uniformPacket μ n (x, hs))
        = μ x * ((∏ j, κ.kernel x (hs j)) *
            ((n : ℝ) * Real.log (Fintype.card H : ℝ) + ∑ j, Real.log (κ.kernel x (hs j)))) := by
    intro x hs
    have hprodpos : (0 : ℝ) < ∏ j, κ.kernel x (hs j) :=
      Finset.prod_pos fun j _ => κ.pos x (hs j)
    rcases eq_or_lt_of_le (hμ x) with hzero | hpos
    · simp only [formedPacket, uniformPacket, depth_kernel, ← hzero]
      ring
    · have hratio : (μ x * ∏ j, κ.kernel x (hs j)) / (μ x * ((Fintype.card H : ℝ)⁻¹) ^ n)
          = (Fintype.card H : ℝ) ^ n * ∏ j, κ.kernel x (hs j) := by
        rw [mul_div_mul_left _ _ hpos.ne', div_eq_iff (by positivity), inv_pow]
        field_simp
      simp only [formedPacket, uniformPacket, depth_kernel]
      rw [hratio, Real.log_mul (by positivity) hprodpos.ne', Real.log_pow,
        Real.log_prod (fun j _ => (κ.pos x (hs j)).ne')]
      ring
  have hinner : ∀ x : X, ∑ hs : Fin n → H, (∏ j, κ.kernel x (hs j)) *
      ((n : ℝ) * Real.log (Fintype.card H : ℝ) + ∑ j, Real.log (κ.kernel x (hs j)))
      = (n : ℝ) * Real.log (Fintype.card H : ℝ)
        + n * ∑ h, κ.kernel x h * Real.log (κ.kernel x h) := by
    intro x
    have hsplit : ∀ hs : Fin n → H, (∏ j, κ.kernel x (hs j)) *
        ((n : ℝ) * Real.log (Fintype.card H : ℝ) + ∑ j, Real.log (κ.kernel x (hs j)))
        = ((n : ℝ) * Real.log (Fintype.card H : ℝ)) * (∏ j, κ.kernel x (hs j))
          + (∏ j, κ.kernel x (hs j)) * (∑ j, Real.log (κ.kernel x (hs j))) := fun hs => by ring
    rw [Finset.sum_congr rfl fun hs _ => hsplit hs, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_prod_eq_one (κ.kernel x) (κ.row x), mul_one,
      sum_prod_mul_sum (κ.kernel x) (κ.row x) (fun h => Real.log (κ.kernel x h))]
  have hrow : ∀ x : X, ∑ hs : Fin n → H,
      κ.formedPacket μ n (x, hs) *
          Real.log (κ.formedPacket μ n (x, hs) / uniformPacket μ n (x, hs))
      = μ x * ((n : ℝ) * Real.log (Fintype.card H : ℝ)
        + n * ∑ h, κ.kernel x h * Real.log (κ.kernel x h)) := by
    intro x
    rw [Finset.sum_congr rfl fun hs _ => hterm x hs, ← Finset.mul_sum, hinner x]
  rw [finiteKL, Fintype.sum_prod_type, Finset.sum_congr rfl fun x _ => hrow x, avgEntropy]
  have hexp : ∀ x : X, μ x * ((n : ℝ) * Real.log (Fintype.card H : ℝ)
        + n * ∑ h, κ.kernel x h * Real.log (κ.kernel x h))
      = ((n : ℝ) * Real.log (Fintype.card H : ℝ)) * μ x
        + (n : ℝ) * (-(μ x * (-∑ h, κ.kernel x h * Real.log (κ.kernel x h)))) := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_add_distrib, ← Finset.mul_sum, hμsum,
    mul_one, ← Finset.mul_sum, Finset.sum_neg_distrib]
  ring

/-- **Recovered latent work** (second summand of card `(RIT.25)`). -/
theorem sum_formedPacket_mul_log_index (μ : X → ℝ) (n : ℕ) :
    ∑ p : X × (Fin n → H), κ.formedPacket μ n p * Real.log ((κ.depth n).index p)
      = n * κ.avgEntropy μ := by
  classical
  have hterm : ∀ (x : X) (hs : Fin n → H),
      κ.formedPacket μ n (x, hs) * Real.log ((κ.depth n).index (x, hs))
        = μ x * ((∏ j, κ.kernel x (hs j)) * (∑ j, -Real.log (κ.kernel x (hs j)))) := by
    intro x hs
    rw [SplitRecovery.depth_index, formedPacket, depth_kernel,
      Real.log_prod (fun j _ => inv_ne_zero (κ.pos x (hs j)).ne')]
    simp only [Real.log_inv]
    ring
  have hrow : ∀ x : X, ∑ hs : Fin n → H,
      κ.formedPacket μ n (x, hs) * Real.log ((κ.depth n).index (x, hs))
      = μ x * ((n : ℝ) * ∑ h, κ.kernel x h * -Real.log (κ.kernel x h)) := by
    intro x
    rw [Finset.sum_congr rfl fun hs _ => hterm x hs, ← Finset.mul_sum,
      sum_prod_mul_sum (κ.kernel x) (κ.row x) (fun h => -Real.log (κ.kernel x h))]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun x _ => hrow x, avgEntropy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hneg : ∑ h, κ.kernel x h * -Real.log (κ.kernel x h)
      = -∑ h, κ.kernel x h * Real.log (κ.kernel x h) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [hneg]
  ring

/-- **Global formation equation of state** (card `(RIT.23)`). -/
theorem formation_equation_of_state [Nonempty H] (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hμsum : ∑ x, μ x = 1) (n : ℕ) :
    finiteKL (κ.formedPacket μ n) (uniformPacket μ n)
        + ∑ p : X × (Fin n → H), κ.formedPacket μ n p * Real.log ((κ.depth n).index p)
      = n * Real.log (Fintype.card H : ℝ) := by
  rw [κ.finiteKL_formedPacket_uniformPacket μ hμ hμsum n,
    κ.sum_formedPacket_mul_log_index μ n]
  ring

/-- **Horizontal information neutrality** (card `(RIT.26)`). -/
theorem finiteKL_formedPacket (μ ν : X → ℝ) (n : ℕ) :
    finiteKL (κ.formedPacket μ n) (κ.formedPacket ν n) = finiteKL μ ν := by
  classical
  have hterm : ∀ (x : X) (hs : Fin n → H),
      κ.formedPacket μ n (x, hs) *
          Real.log (κ.formedPacket μ n (x, hs) / κ.formedPacket ν n (x, hs))
        = (μ x * Real.log (μ x / ν x)) * ∏ j, κ.kernel x (hs j) := by
    intro x hs
    have hprodpos : (0 : ℝ) < ∏ j, κ.kernel x (hs j) :=
      Finset.prod_pos fun j _ => κ.pos x (hs j)
    simp only [formedPacket, depth_kernel]
    rw [mul_div_mul_right _ _ hprodpos.ne']
    ring
  have hrow : ∀ x : X, ∑ hs : Fin n → H,
      κ.formedPacket μ n (x, hs) *
        Real.log (κ.formedPacket μ n (x, hs) / κ.formedPacket ν n (x, hs))
      = μ x * Real.log (μ x / ν x) := by
    intro x
    rw [Finset.sum_congr rfl fun hs _ => hterm x hs, ← Finset.mul_sum,
      sum_prod_eq_one (κ.kernel x) (κ.row x), mul_one]
  rw [finiteKL, Fintype.sum_prod_type, Finset.sum_congr rfl fun x _ => hrow x, finiteKL]

end SplitRecovery

end EquationOfState

end

end GaloisForLFunctions.HTGeometry
