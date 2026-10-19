import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiBankPacketNormalizedGram
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiDyadicAntichainSupportRepresentation

/-!
# Divergent prime capacity: positive antichain packets with unbounded energy ratio

Take `L ≥ 2` disjoint nonempty banks of allowed odd primes whose parity ratios
are below `1/(4L)`. The one-hot parity packet of bank `t` is placed at dyadic
level `t+1`, with normalized amplitude `1` for the first bank and `1/2` for the
others. Distinct one-hot packets have disjoint supports, so every odd index
carries one level: the literal coefficient packet is a nonnegative dyadic
antichain whose odd parts use only bank primes.

Along the normalized ray the state at level `k ≤ L` is a convex combination
of the normalized packets, and the state doubles its decay beyond level `L`.
Since every normalized Gram entry lies in `[1 - 1/L, 1]`, each of the first `L`
states has squared norm at least `1 - 1/L`, each interior selected difference
has squared norm at most `1/(2L)`, and the geometric tail contributes exactly one
third of the terminal squared norm. Hence

* `P_h ≥ L - 1` and `0 < Q_h ≤ (L-1)/(2L) + 1/3`;
* `P ≥ (L-1)/2` and `0 < Q < 5/6` for the native reciprocal-pronic energies.
-/

open scoped BigOperators
open Finset GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

section Form

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def bankForm (G : ι → ι → ℝ) (γ : ι → ℝ) : ℝ := ∑ j, ∑ k, γ j * γ k * G j k

omit [DecidableEq ι] in
private theorem bankForm_smul (G : ι → ι → ℝ) (c : ℝ) (γ : ι → ℝ) :
    bankForm G (fun j => c * γ j) = c^2 * bankForm G γ := by
  unfold bankForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] in
private theorem bankForm_convex (G : ι → ι → ℝ) {ε : ℝ}
    (hG : ∀ j k, 1 - ε ≤ G j k ∧ G j k ≤ 1) (γ : ι → ℝ) (hγ : ∀ j, 0 ≤ γ j)
    (hs : ∑ j, γ j = 1) :
    1 - ε ≤ bankForm G γ ∧ bankForm G γ ≤ 1 ∧ ∀ t, 1 - ε ≤ ∑ j, γ j * G j t := by
  have hsq : ∑ j, ∑ k, γ j * γ k = 1 := by
    rw [← Finset.sum_mul_sum, hs, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · calc
      1 - ε = (∑ j, ∑ k, γ j * γ k) * (1 - ε) := by rw [hsq, one_mul]
      _ = ∑ j, ∑ k, γ j * γ k * (1 - ε) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_mul _ _ _)
      _ ≤ bankForm G γ := Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (hG j k).1 (mul_nonneg (hγ j) (hγ k))))
  · calc
      bankForm G γ ≤ ∑ j, ∑ k, γ j * γ k * 1 := Finset.sum_le_sum (fun j _ =>
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hG j k).2 (mul_nonneg (hγ j) (hγ k))))
      _ = 1 := by simp only [mul_one, hsq]
  · intro t
    calc
      1 - ε = ∑ j, γ j * (1 - ε) := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ ∑ j, γ j * G j t :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hG j t).1 (hγ j))

private theorem bankForm_half_sub_single (G : ι → ι → ℝ) (hG : ∀ j k, G j k = G k j)
    (γ : ι → ℝ) (t : ι) :
    bankForm G (fun j => γ j / 2 - if j = t then 1 / 2 else 0) =
      (bankForm G γ - 2 * ∑ j, γ j * G j t + G t t) / 4 := by
  unfold bankForm
  have h1 (j k : ι) :
      (γ j / 2 - if j = t then 1 / 2 else 0) * (γ k / 2 - if k = t then 1 / 2 else 0) * G j k =
        γ j * γ k * G j k / 4 - (if k = t then γ j * G j k / 4 else 0) -
          (if j = t then γ k * G j k / 4 else 0) +
          (if j = t then (if k = t then G j k / 4 else 0) else 0) := by
    split_ifs <;> ring
  have e1 : ∑ j, ∑ k, (if k = t then γ j * G j k / 4 else 0) = ∑ j, γ j * G j t / 4 := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e2 : ∑ j, ∑ k, (if j = t then γ k * G j k / 4 else 0) = ∑ j, γ j * G j t / 4 := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl (fun j _ => by rw [hG])
  have e3 : ∑ j, ∑ k, (if j = t then (if k = t then G j k / 4 else 0) else 0) = G t t / 4 := by
    rw [Finset.sum_eq_single t (fun j _ hj => by simp [hj]) (fun h => (h (Finset.mem_univ t)).elim)]
    simp
  simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e2, e3]
  simp only [← Finset.sum_div]
  ring

end Form

/-! ### Level amplitudes and the normalized trajectory -/

/-- Normalized input amplitude of bank `t`: `1` for the first bank, `1/2` afterwards. -/
def fermiBankLevelAmplitude (t : ℕ) : ℝ := if t = 0 then 1 else 1 / 2

/-- Coefficient of bank `t`, placed at dyadic level `t+1`, in the normalized ray state `k`. -/
def fermiBankTrajectory (k t : ℕ) : ℝ := fermiDyadicImpulse (t + 1) k * fermiBankLevelAmplitude t

theorem fermiBankTrajectory_nonneg (k t : ℕ) : 0 ≤ fermiBankTrajectory k t := by
  unfold fermiBankTrajectory fermiDyadicImpulse fermiBankLevelAmplitude
  split_ifs <;> positivity

theorem fermiBankTrajectory_zero (t : ℕ) : fermiBankTrajectory 0 t = 0 := by
  simp [fermiBankTrajectory, fermiDyadicImpulse]

/-- One level step halves the old state and inserts the next bank with amplitude `1/2`. -/
theorem fermiBankTrajectory_succ {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    fermiBankTrajectory (k + 1) t =
      fermiBankTrajectory k t / 2 + if t = k then 1 / 2 else 0 := by
  unfold fermiBankTrajectory fermiDyadicImpulse
  rcases lt_trichotomy t k with h | h | h
  · simp only [show t + 1 ≤ k + 1 by omega, show t + 1 ≤ k by omega, show t ≠ k by omega,
      if_true, if_false, add_zero, pow_succ]
    field_simp
  · subst h
    simp [fermiBankLevelAmplitude, show t ≠ 0 by omega]
  · simp [show ¬ t + 1 ≤ k + 1 by omega, show ¬ t + 1 ≤ k by omega, show t ≠ k by omega]

/-- The first `L` normalized states are convex combinations of the bank packets. -/
theorem fermiBankTrajectory_sum {L k : ℕ} (hk1 : 1 ≤ k) (hkL : k ≤ L) :
    ∑ t ∈ Finset.range L, fermiBankTrajectory k t = 1 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      rw [Finset.sum_eq_single 0]
      · simp [fermiBankTrajectory, fermiDyadicImpulse, fermiBankLevelAmplitude]
      · intro t _ ht
        simp [fermiBankTrajectory, fermiDyadicImpulse, show ¬ t + 1 ≤ 1 by omega]
      · intro h
        exact (h (Finset.mem_range.mpr (by omega))).elim
    · have hsum := ih hpos (by omega)
      simp only [fermiBankTrajectory_succ hpos, Finset.sum_add_distrib, ← Finset.sum_div, hsum,
        Finset.sum_ite_eq', Finset.mem_range, show k < L by omega, if_true]
      norm_num

/-- Beyond the last bank the normalized state halves at every level. -/
theorem fermiBankTrajectory_tail {L : ℕ} (r : ℕ) {t : ℕ} (ht : t < L) :
    fermiBankTrajectory (r + L) t = (1 / 2 : ℝ)^r * fermiBankTrajectory L t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show r + 1 + L = (r + L) + 1 by omega, fermiBankTrajectory_succ (by omega),
      if_neg (by omega), ih, pow_succ]
    ring

/-! ### The literal bank packet -/

section Packet

variable {L : ℕ}

/-- Normalization scale `H₀^{-1/2}` with `H₀ = Z ∏ E_t`. -/
def fermiBankPacketScale (T : Fin L → Finset ℕ) : ℝ :=
  (Real.sqrt (fermiOddHomogeneousMass * ∏ i, fermiBankParityClassMass (T i)))⁻¹

/-- Dyadic level carried by a cube point: `t+1` on the support of the packet `t`. -/
def fermiBankPacketDepth (T : Fin L → Finset ℕ) (x : ∀ i, T i → Bool) : ℕ :=
  ∑ t : Fin L, if fermiOneHotBankPacket T t x = 1 then (t : ℕ) + 1 else 0

/-- Normalized amplitude carried by a cube point. -/
def fermiBankPacketAmplitude (T : Fin L → Finset ℕ) (x : ∀ i, T i → Bool) : ℝ :=
  fermiBankPacketScale T * ∑ t : Fin L, fermiBankLevelAmplitude t * fermiOneHotBankPacket T t x

/-- The literal nonnegative dyadic-antichain packet built from the bank packets. -/
def fermiBankAntichainCoefficient (T : Fin L → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hdisj : Pairwise (fun i k => Disjoint (T i) (T k))) : ℕ → ℝ :=
  fermiDyadicAntichainCoefficient (fermiBankCubeSupport T)
    (fun d => fermiBankPacketDepth T ((fermiBankCubeEquiv T hT hdisj).symm d))
    (fun d => fermiBankPacketAmplitude T ((fermiBankCubeEquiv T hT hdisj).symm d))

/-- A horizon containing every literal index of the bank packet. -/
def fermiBankAntichainHorizon (T : Fin L → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hdisj : Pairwise (fun i k => Disjoint (T i) (T k))) : ℕ :=
  ∑ d : fermiBankCubeSupport T,
    2 ^ fermiBankPacketDepth T ((fermiBankCubeEquiv T hT hdisj).symm d) * (d : ℕ)

private theorem packet_cases (T : Fin L → Finset ℕ) (x : ∀ i, T i → Bool) :
    (∀ t, fermiOneHotBankPacket T t x = 0) ∨
      ∃ t₀, fermiOneHotBankPacket T t₀ x = 1 ∧ ∀ t, t ≠ t₀ → fermiOneHotBankPacket T t x = 0 := by
  by_cases h : ∃ t₀, fermiOneHotBankPacket T t₀ x = 1
  · obtain ⟨t₀, ht₀⟩ := h
    refine Or.inr ⟨t₀, ht₀, fun t ht => ?_⟩
    have hd := fermiOneHotBankPacket_disjoint T ht x
    rw [mul_comm, ht₀, one_mul] at hd
    exact hd
  · refine Or.inl (fun t => ?_)
    exact (fermiOneHotBankPacket_zero_or_one T t x).resolve_right (fun h1 => h ⟨t, h1⟩)

/-- Literal native coordinates are the normalized bank combinations. -/
theorem fermiBankPacket_coordinate (T : Fin L → Finset ℕ) (φ : ℕ → ℝ)
    (x : ∀ i, T i → Bool) :
    φ (fermiBankPacketDepth T x) * fermiBankPacketAmplitude T x =
      fermiBankPacketScale T * ∑ t : Fin L, (φ ((t : ℕ) + 1) * fermiBankLevelAmplitude t) *
        fermiOneHotBankPacket T t x := by
  unfold fermiBankPacketDepth fermiBankPacketAmplitude
  rcases packet_cases T x with h | ⟨t₀, h₀, h⟩
  · simp [h]
  · rw [Finset.sum_eq_single t₀ (fun t _ ht => by rw [if_neg (by rw [h t ht]; norm_num)])
      (fun h' => (h' (Finset.mem_univ _)).elim), if_pos h₀,
      Finset.sum_eq_single t₀ (fun t _ ht => by rw [h t ht, mul_zero])
        (fun h' => (h' (Finset.mem_univ _)).elim),
      Finset.sum_eq_single t₀ (fun t _ ht => by rw [h t ht, mul_zero])
        (fun h' => (h' (Finset.mem_univ _)).elim), h₀]
    ring

theorem fermiBankPacketAmplitude_nonneg (T : Fin L → Finset ℕ) (x : ∀ i, T i → Bool) :
    0 ≤ fermiBankPacketAmplitude T x := by
  unfold fermiBankPacketAmplitude fermiBankPacketScale
  apply mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply Finset.sum_nonneg
  intro t _
  apply mul_nonneg
  · unfold fermiBankLevelAmplitude
    split_ifs <;> norm_num
  · rcases fermiOneHotBankPacket_zero_or_one T t x with h | h <;> simp [h]

variable (T : Fin L → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
  (hodd : ∀ i, ∀ p ∈ T i, Odd p) (hdisj : Pairwise (fun i k => Disjoint (T i) (T k)))
  (hne : ∀ i, (T i).Nonempty)

include hodd hne in
/-- Every native profile energy of the bank packet is the normalized bank Gram form. -/
private theorem bank_profile_energy (φ : ℕ → ℝ) :
    (∑' m : ℕ, (fermiOddDivisorPacket (fermiBankCubeSupport T)
      (fun d => φ (fermiBankPacketDepth T ((fermiBankCubeEquiv T hT hdisj).symm d)) *
        fermiBankPacketAmplitude T ((fermiBankCubeEquiv T hT hdisj).symm d)) m)^2) =
      bankForm (fermiBankNormalizedGram T)
        (fun t : Fin L => φ ((t : ℕ) + 1) * fermiBankLevelAmplitude t) ∧
    0 ≤ bankForm (fermiBankNormalizedGram T)
        (fun t : Fin L => φ ((t : ℕ) + 1) * fermiBankLevelAmplitude t) := by
  have hc : (fun d : fermiBankCubeSupport T =>
      φ (fermiBankPacketDepth T ((fermiBankCubeEquiv T hT hdisj).symm d)) *
        fermiBankPacketAmplitude T ((fermiBankCubeEquiv T hT hdisj).symm d)) =
      fun d => (Real.sqrt (fermiOddHomogeneousMass * ∏ i, fermiBankParityClassMass (T i)))⁻¹ *
        ∑ t : Fin L, (φ ((t : ℕ) + 1) * fermiBankLevelAmplitude t) *
          fermiOneHotBankPacket T t ((fermiBankCubeEquiv T hT hdisj).symm d) := by
    funext d
    exact fermiBankPacket_coordinate T φ _
  have h := (fermiOneHotBank_native_gram T hT hodd hdisj hne
    (fun t : Fin L => φ ((t : ℕ) + 1) * fermiBankLevelAmplitude t)).2
  rw [hc, h]
  refine ⟨rfl, ?_⟩
  unfold bankForm
  rw [← h]
  exact tsum_nonneg (fun m => sq_nonneg _)

private theorem trajectory_form (φ : ℕ → ℝ) (k : ℕ) (hφ : ∀ n, φ n = fermiDyadicImpulse n k) :
    (fun t : Fin L => φ ((t : ℕ) + 1) * fermiBankLevelAmplitude t) =
      fun t : Fin L => fermiBankTrajectory k t := by
  funext t
  rw [hφ]
  rfl

include hodd in
/-- The bank packet is a nonnegative admissible dyadic antichain over the allowed primes. -/
theorem fermiBankAntichainCoefficient_admissible (allowed : Set ℕ)
    (hallowed : ∀ i, ∀ p ∈ T i, p ∈ allowed) (N : ℕ) :
    fermiDyadicAntichainAdmissible allowed N (fermiBankAntichainCoefficient T hT hdisj) ∧
      ∀ n, 0 ≤ fermiBankAntichainCoefficient T hT hdisj n := by
  refine ⟨fermiDyadicAntichainCoefficient_admissible allowed N _ _ _
    (fermiBankCubeSupport_odd T hodd) (fun d hd p hp => ?_), fun n => ?_⟩
  · obtain ⟨i, hi⟩ := fermiBankCubeSupport_primeFactors T hT d hd p hp
    exact hallowed i p hi
  · exact fermiDyadicAntichainCoefficient_nonneg _ _ _
      (fun d => fermiBankPacketAmplitude_nonneg T _) n

theorem fermiBankAntichainHorizon_le (d : fermiBankCubeSupport T) :
    2 ^ fermiBankPacketDepth T ((fermiBankCubeEquiv T hT hdisj).symm d) * (d : ℕ) ≤
      fermiBankAntichainHorizon T hT hdisj :=
  Finset.single_le_sum (f := fun d : fermiBankCubeSupport T =>
    2 ^ fermiBankPacketDepth T ((fermiBankCubeEquiv T hT hdisj).symm d) * (d : ℕ))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)

include hodd hne in
/-- Homogeneous bounds for the bank packet: `P_h ≥ L-1` and `0 < Q_h ≤ (L-1)/(2L)+1/3`. -/
theorem fermiBankAntichain_homogeneous_bounds (hL : 2 ≤ L)
    (hθ : ∀ i, fermiPrimeBankParityRatio (T i) < 1 / (4 * (L : ℝ))) :
    (L : ℝ) - 1 ≤ sieveHomogeneousEnergy (fermiBankAntichainHorizon T hT hdisj)
        (fermiBankAntichainCoefficient T hT hdisj) ∧
      0 < fermiSelectedHomogeneousEnergy (fermiBankAntichainHorizon T hT hdisj)
        (fermiBankAntichainCoefficient T hT hdisj) ∧
      fermiSelectedHomogeneousEnergy (fermiBankAntichainHorizon T hT hdisj)
        (fermiBankAntichainCoefficient T hT hdisj) ≤ ((L : ℝ) - 1) / (2 * L) + 1 / 3 := by
  set N := fermiBankAntichainHorizon T hT hdisj
  set S := fermiBankCubeSupport T
  set e := fermiBankCubeEquiv T hT hdisj
  set G := fermiBankNormalizedGram T
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hG : ∀ j k, 1 - 1 / (L : ℝ) ≤ G j k ∧ G j k ≤ 1 :=
    fermiBankNormalizedGram_bounds T hT (by linarith) hθ
  have hGs : ∀ j k, G j k = G k j := fermiBankNormalizedGram_symm T
  let β : ℕ → Fin L → ℝ := fun k t => fermiBankTrajectory k t
  have hβsum {k : ℕ} (hk1 : 1 ≤ k) (hkL : k ≤ L) : ∑ t, β k t = 1 := by
    simp only [β]
    rw [Fin.sum_univ_eq_sum_range (fun t => fermiBankTrajectory k t) L]
    exact fermiBankTrajectory_sum hk1 hkL
  have hconv {k : ℕ} (hk1 : 1 ≤ k) (hkL : k ≤ L) :=
    bankForm_convex G hG (β k) (fun t => fermiBankTrajectory_nonneg k t) (hβsum hk1 hkL)
  have hSodd := fermiBankCubeSupport_odd T hodd
  have hN := fermiBankAntichainHorizon_le T hT hdisj
  -- full homogeneous energy
  obtain ⟨hPs, hPe⟩ := fermiDyadicAntichain_homogeneousEnergy N S
    (fun d => fermiBankPacketDepth T (e.symm d)) (fun d => fermiBankPacketAmplitude T (e.symm d))
    hSodd hN
  have hPk (k : ℕ) := bank_profile_energy T hT hodd hdisj hne (fun n => fermiDyadicImpulse n k)
  have hPform (k : ℕ) : (∑' m : ℕ, (fermiOddDivisorPacket S
      (fun d => fermiDyadicImpulse (fermiBankPacketDepth T (e.symm d)) k *
        fermiBankPacketAmplitude T (e.symm d)) m)^2) = bankForm G (β k) :=
    (hPk k).1.trans (by rw [trajectory_form _ k (fun n => rfl)])
  have hPnn (k : ℕ) : 0 ≤ bankForm G (β k) := by
    rw [← hPform k]
    exact tsum_nonneg (fun m => sq_nonneg _)
  simp only [hPform] at hPs hPe
  -- selected homogeneous energy
  obtain ⟨hQs, hQe⟩ := fermiDyadicAntichain_selectedHomogeneousEnergy N S
    (fun d => fermiBankPacketDepth T (e.symm d)) (fun d => fermiBankPacketAmplitude T (e.symm d))
    hSodd hN
  let δ : ℕ → Fin L → ℝ := fun k t => β (k + 1) t - β (k + 2) t
  have hQform (k : ℕ) : (∑' m : ℕ, (fermiOddDivisorPacket S
      (fun d => (fermiDyadicImpulse (fermiBankPacketDepth T (e.symm d)) (k + 1) -
        fermiDyadicImpulse (fermiBankPacketDepth T (e.symm d)) (k + 2)) *
        fermiBankPacketAmplitude T (e.symm d)) m)^2) = bankForm G (δ k) := by
    rw [(bank_profile_energy T hT hodd hdisj hne
      (fun n => fermiDyadicImpulse n (k + 1) - fermiDyadicImpulse n (k + 2))).1]
    congr 1
    funext t
    simp only [δ, β, fermiBankTrajectory]
    ring
  have hQnn (k : ℕ) : 0 ≤ bankForm G (δ k) := by
    rw [← hQform k]
    exact tsum_nonneg (fun m => sq_nonneg _)
  have hQ0 : (∑' m : ℕ, (fermiOddDivisorPacket S
      (fun d => fermiDyadicImpulse (fermiBankPacketDepth T (e.symm d)) 0 *
        fermiBankPacketAmplitude T (e.symm d)) m)^2) = 0 := by
    rw [(hPk 0).1]
    unfold bankForm
    simp [fermiDyadicImpulse]
  simp only [hQform] at hQs hQe
  rw [hQ0, zero_add] at hQe
  -- interior differences
  have hint {k : ℕ} (hk : k + 1 < L) : bankForm G (δ k) ≤ 1 / (2 * L) := by
    have hδ : δ k = fun t => β (k + 1) t / 2 - if t = (⟨k + 1, hk⟩ : Fin L) then 1 / 2 else 0 := by
      funext t
      simp only [δ, β]
      rw [show k + 2 = (k + 1) + 1 by omega, fermiBankTrajectory_succ (k := k + 1) (by omega)]
      by_cases ht : t = (⟨k + 1, hk⟩ : Fin L)
      · subst ht
        simp only [if_true]
        ring
      · rw [if_neg ht, if_neg (fun h => ht (Fin.ext h))]
        ring
    obtain ⟨-, hup, hcross⟩ := hconv (k := k + 1) (by omega) hk.le
    rw [hδ, bankForm_half_sub_single G hGs]
    have hdiag : G ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ = 1 := by simp [G, fermiBankNormalizedGram]
    have hc := hcross ⟨k + 1, hk⟩
    rw [hdiag]
    have : (1 : ℝ) / L = 2 * (1 / (2 * L)) := by field_simp
    linarith
  -- geometric tail beyond the last bank
  have htail (r : ℕ) : bankForm G (δ (r + (L - 1))) =
      bankForm G (β L) / 4 * (1 / 4 : ℝ)^r := by
    have hδ : δ (r + (L - 1)) = fun t => (1 / 2 : ℝ)^(r + 1) * β L t := by
      funext t
      simp only [δ, β]
      rw [show r + (L - 1) + 1 = r + L by omega, show r + (L - 1) + 2 = (r + 1) + L by omega,
        fermiBankTrajectory_tail r t.2, fermiBankTrajectory_tail (r + 1) t.2]
      ring
    rw [hδ, bankForm_smul, ← pow_mul, show (r + 1) * 2 = 2 * (r + 1) by ring, pow_mul]
    norm_num
    ring
  have htailsum : HasSum (fun r : ℕ => bankForm G (δ (r + (L - 1)))) (bankForm G (β L) / 3) := by
    have hg := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (bankForm G (β L) / 4)
    have hv : bankForm G (β L) / 4 * (1 - 1 / 4)⁻¹ = bankForm G (β L) / 3 := by ring
    rw [hv] at hg
    simp only [htail]
    exact hg
  have hsplit := hQs.sum_add_tsum_nat_add (L - 1)
  rw [htailsum.tsum_eq] at hsplit
  have hinter : ∑ k ∈ Finset.range (L - 1), bankForm G (δ k) ≤ ((L : ℝ) - 1) / (2 * L) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (L - 1), (1 / (2 * (L : ℝ))) :=
        Finset.sum_le_sum (fun k hk => hint (by have := Finset.mem_range.mp hk; omega))
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega)]
        ring
  have hinter0 : 0 ≤ ∑ k ∈ Finset.range (L - 1), bankForm G (δ k) :=
    Finset.sum_nonneg (fun k _ => hQnn k)
  obtain ⟨hLlow, hLup, -⟩ := hconv (k := L) (by omega) le_rfl
  have hL1 : (0 : ℝ) < 1 - 1 / L := by
    have : (1 : ℝ) / L ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hLr
    linarith
  have hcoef : fermiBankAntichainCoefficient T hT hdisj =
      fermiDyadicAntichainCoefficient S (fun d => fermiBankPacketDepth T (e.symm d))
        (fun d => fermiBankPacketAmplitude T (e.symm d)) := rfl
  rw [hcoef]
  refine ⟨?_, ?_, ?_⟩
  · rw [hPe]
    calc
      (L : ℝ) - 1 = ∑ k ∈ Finset.Icc 1 L, (1 - 1 / (L : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show L + 1 - 1 = L by omega]
        field_simp
      _ ≤ ∑ k ∈ Finset.Icc 1 L, bankForm G (β k) := Finset.sum_le_sum (fun k hk =>
        (hconv (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2).1)
      _ ≤ _ := hPs.sum_le_tsum _ (fun k _ => hPnn k)
  · rw [hQe, ← hsplit]
    have : 0 < bankForm G (β L) / 3 := by linarith
    linarith
  · rw [hQe, ← hsplit]
    linarith

include hodd hne in
/-- Native physical bounds for the bank packet: `P ≥ (L-1)/2` and `0 < Q < 5/6`. -/
theorem fermiBankAntichain_physical_bounds (hL : 2 ≤ L)
    (hθ : ∀ i, fermiPrimeBankParityRatio (T i) < 1 / (4 * (L : ℝ))) :
    ((L : ℝ) - 1) / 2 ≤ sieveTotalPronicEnergy (fermiBankAntichainHorizon T hT hdisj)
        (fermiBankAntichainCoefficient T hT hdisj) ∧
      0 < fermiSelectedTotalPronicEnergy (fermiBankAntichainHorizon T hT hdisj)
        (fermiBankAntichainCoefficient T hT hdisj) ∧
      fermiSelectedTotalPronicEnergy (fermiBankAntichainHorizon T hT hdisj)
        (fermiBankAntichainCoefficient T hT hdisj) < 5 / 6 := by
  obtain ⟨hP, hQ0, hQ1⟩ := fermiBankAntichain_homogeneous_bounds T hT hodd hdisj hne hL hθ
  have hp := sieveHomogeneousEnergy_pronic_bounds (fermiBankAntichainHorizon T hT hdisj)
    (fermiBankAntichainCoefficient T hT hdisj)
  have hq := fermiSelectedHomogeneousEnergy_pronic_bounds (fermiBankAntichainHorizon T hT hdisj)
    (fermiBankAntichainCoefficient T hT hdisj)
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hfrac : ((L : ℝ) - 1) / (2 * L) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  refine ⟨by linarith [hp.1], by linarith [hq.1], by linarith [hq.2]⟩

end Packet

/-- Divergent reciprocal capacity yields, for every `L ≥ 2`, a nonnegative admissible
dyadic-antichain packet with `P ≥ (L-1)/2` and `0 < Q < 5/6`. -/
theorem exists_fermiDyadicAntichain_divergentCapacity_packet (allowed : Set ℕ)
    (hallowed : ∀ p ∈ allowed, p.Prime ∧ Odd p)
    (hdiv : ∀ M : ℝ, ∃ P : Finset ℕ, (∀ p ∈ P, p ∈ allowed) ∧ M < ∑ p ∈ P, 1 / (p : ℝ))
    {L : ℕ} (hL : 2 ≤ L) :
    ∃ (N : ℕ) (c : ℕ → ℝ), fermiDyadicAntichainAdmissible allowed N c ∧ (∀ n, 0 ≤ c n) ∧
      ((L : ℝ) - 1) / 2 ≤ sieveTotalPronicEnergy N c ∧
      0 < fermiSelectedTotalPronicEnergy N c ∧ fermiSelectedTotalPronicEnergy N c < 5 / 6 := by
  obtain ⟨T, hdisj, hbank⟩ := exists_fermiSmallParityRatioBanks allowed
    (fun p hp => (hallowed p hp).1) hdiv (show 0 < L by omega)
  have hT : ∀ i, ∀ p ∈ T i, p.Prime := fun i p hp => (hallowed p ((hbank i).2.1 p hp)).1
  have hodd : ∀ i, ∀ p ∈ T i, Odd p := fun i p hp => (hallowed p ((hbank i).2.1 p hp)).2
  have hne : ∀ i, (T i).Nonempty := fun i => (hbank i).1
  obtain ⟨hadm, hnn⟩ := fermiBankAntichainCoefficient_admissible T hT hodd hdisj allowed
    (fun i => (hbank i).2.1) (fermiBankAntichainHorizon T hT hdisj)
  exact ⟨fermiBankAntichainHorizon T hT hdisj, fermiBankAntichainCoefficient T hT hdisj, hadm,
    hnn, fermiBankAntichain_physical_bounds T hT hodd hdisj hne hL (fun i => (hbank i).2.2.2)⟩

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
