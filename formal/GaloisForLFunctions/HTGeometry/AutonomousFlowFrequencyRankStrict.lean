import GaloisForLFunctions.HTGeometry.InvarianceOfDomain
import GaloisForLFunctions.HTGeometry.PhaseRankDimensionBound
import GaloisForLFunctions.HTGeometry.CarrierTranslationEquivariance

/-!
# Strict frequency rank from locally unique autonomous transport

O'Brien's strict form of the frequency-rank law uses more than a finite-dimensional carrier
embedding. If the frequency rank filled the ambient state dimension, invariance of domain would
give one open patch of the carrier image. Local autonomous evolution transports that patch to every
point of the image. The compact carrier image would therefore be a nonempty clopen subset of a
Euclidean space, hence the whole (unbounded) space, a contradiction.

`HasLocalAmbientCarrierTransport` isolates exactly the local-flow input: near every carrier state,
each time translation is represented by a continuous injective ambient map. No global flow on the
whole ambient space is required.
-/

open Metric Set Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {f : ℝ →ᵇ ℂ}

/-- Local ambient realization of every carrier translation. This is the topological consequence
of locally unique autonomous evolution used by the Cartwright--O'Brien argument. -/
def HasLocalAmbientCarrierTransport (f : ℝ →ᵇ ℂ) {d : ℕ}
    (J : BohrHull f → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ (t : ℝ) (x : BohrHull f),
    ∃ (V : Set (EuclideanSpace ℝ (Fin d)))
      (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsOpen V ∧ J x ∈ V ∧ ContinuousOn T V ∧ Set.InjOn T V ∧
        ∀ y : BohrHull f, J y ∈ V → T (J y) = J (y + bohrIota f t)

private theorem false_of_full_independent_frequencies_of_local_ambient_transport
    (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {d : ℕ} {lam : Fin d → ℝ} (hind : LinearIndependent ℚ lam)
    (hlam : ∀ j, IsBohrHullFrequency f (lam j))
    (hd : 0 < d)
    (J : BohrHull f → EuclideanSpace ℝ (Fin d))
    (hJcont : Continuous J) (hJinj : Function.Injective J)
    (htransport : HasLocalAmbientCarrierTransport f J) : False := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  obtain ⟨phi, hphicont, hphival⟩ :=
    exists_continuous_hullParameter hf htb hind hlam
  let c : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))
  let U : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ j, x j ∈ Ioo (0 : ℝ) 1}
  have hUopen : IsOpen U := by
    have hUeq : U = ⋂ j : Fin d, (fun x : EuclideanSpace ℝ (Fin d) => x j) ⁻¹' Ioo 0 1 := by
      ext x
      simp [U]
    rw [hUeq]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ j)
  have hcU : c ∈ U := by
    intro j
    norm_num [c, U]
  have hUcube : U ⊆ unitCube d := by
    intro x hx j
    exact ⟨(hx j).1.le, (hx j).2.le⟩
  let psi : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x => J (phi (fun j => Real.pi * x j))
  have hpsicont : Continuous psi := by
    exact hJcont.comp (hphicont.comp
      (continuous_pi fun j => continuous_const.mul (PiLp.continuous_apply 2 _ j)))
  have hpsiinj : Set.InjOn psi (unitCube d) := by
    intro x hx y hy hxy
    have hphieq : phi (fun j => Real.pi * x j) = phi (fun j => Real.pi * y j) :=
      hJinj hxy
    refine PiLp.ext fun j => ?_
    have hchar := congrArg (bohrHullChar f (lam j)) hphieq
    rw [hphival, hphival] at hchar
    rw [Complex.exp_eq_exp_iff_exists_int] at hchar
    obtain ⟨k, hk⟩ := hchar
    have hk' := congrArg (fun z : ℂ => z * (-Complex.I)) hk
    ring_nf at hk'
    have him := congrArg Complex.re hk'
    norm_num at him
    have hxy : x j - y j = 2 * (k : ℝ) := by
      apply (mul_left_cancel₀ Real.pi_ne_zero)
      nlinarith
    have hklo : -(1 : ℝ) ≤ x j - y j := by linarith [(hx j).1, (hy j).2]
    have hkhi : x j - y j ≤ 1 := by linarith [(hx j).2, (hy j).1]
    have hkzero : k = 0 := by
      have hklo' : -(1 : ℝ) / 2 ≤ (k : ℝ) := by linarith
      have hkhi' : (k : ℝ) ≤ 1 / 2 := by linarith
      have hkneg : -(1 : ℝ) < (k : ℝ) := lt_of_lt_of_le (by norm_num) hklo'
      have hkpos : (k : ℝ) < 1 := lt_of_le_of_lt hkhi' (by norm_num)
      have hkneg' : (-1 : ℤ) < k := by exact_mod_cast hkneg
      have hkpos' : k < (1 : ℤ) := by exact_mod_cast hkpos
      omega
    rw [hkzero] at hxy
    have : x j - y j = 0 := by simpa using hxy
    exact sub_eq_zero.mp this
  have hpsiUinj : Set.InjOn psi U := hpsiinj.mono hUcube
  let G : Set (EuclideanSpace ℝ (Fin d)) := psi '' U
  have hGopen : IsOpen G :=
    invariance_of_domain_open_map psi U hUopen hpsicont.continuousOn hpsiUinj
  have hGne : G.Nonempty := ⟨psi c, ⟨c, hcU, rfl⟩⟩
  have hGsub : G ⊆ Set.range J := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨phi (fun j => Real.pi * x j), rfl⟩
  have hopenRange : IsOpen (Set.range J) := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨z, rfl⟩
    have hpreopen : IsOpen (J ⁻¹' G) := hGopen.preimage hJcont
    have hprene : (J ⁻¹' G).Nonempty := by
      obtain ⟨q, hq⟩ := hGne
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨phi (fun j => Real.pi * x j), ⟨x, hx, rfl⟩⟩
    obtain ⟨t, ht⟩ := (denseRange_bohrIota_add f z).exists_mem_open hpreopen hprene
    obtain ⟨V, T, hVopen, hJV, hTcont, hTinj, hTJ⟩ :=
      htransport (-t) (z + bohrIota f t)
    let W : Set (EuclideanSpace ℝ (Fin d)) := G ∩ V
    have hWopen : IsOpen W := hGopen.inter hVopen
    have hJW : J (z + bohrIota f t) ∈ W := ⟨ht, hJV⟩
    refine ⟨T '' W, ⟨?_, ?_, ?_⟩⟩
    · rintro q ⟨u, ⟨huG, huV⟩, rfl⟩
      obtain ⟨x, hx⟩ := hGsub huG
      refine ⟨x + bohrIota f (-t), ?_⟩
      rw [← hTJ x ?_]
      · exact congrArg T hx
      · rwa [hx]
    · exact invariance_of_domain_open_map T W hWopen
        (hTcont.mono inter_subset_right) (hTinj.mono inter_subset_right)
    · refine ⟨J (z + bohrIota f t), hJW, ?_⟩
      rw [hTJ _ hJV]
      congr 1
      rw [add_assoc, ← bohrIota_add]
      simp
  have hcompactRange : IsCompact (Set.range J) := isCompact_range hJcont
  have hclopen : IsClopen (Set.range J) := ⟨hcompactRange.isClosed, hopenRange⟩
  have hneRange : (Set.range J).Nonempty := ⟨J 0, ⟨0, rfl⟩⟩
  have huniv : Set.range J = Set.univ := hclopen.eq_univ hneRange
  have hbounded : Bornology.IsBounded (Set.univ : Set (EuclideanSpace ℝ (Fin d))) := by
    rw [← huniv]
    exact hcompactRange.isBounded
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall
    (s := Set.univ) (0 : EuclideanSpace ℝ (Fin d))).mp hbounded
  let j : Fin d := ⟨0, hd⟩
  let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single j (|r| + 1))
  have hvnorm : ‖v‖ = |r| + 1 := by
    rw [show v = PiLp.single 2 j (|r| + 1) by rfl,
      PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hvball := hr (Set.mem_univ v)
  rw [mem_closedBall_zero_iff, hvnorm] at hvball
  linarith [le_abs_self r]

/-- A locally unique autonomous evolution in a positive-dimensional ambient state space forces
strictly fewer independent carrier frequencies than ambient real dimensions. -/
theorem independent_frequencies_lt_of_local_ambient_transport
    (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {r d : ℕ} {lam : Fin r → ℝ} (hind : LinearIndependent ℚ lam)
    (hlam : ∀ j, IsBohrHullFrequency f (lam j))
    (hd : 0 < d)
    (J : BohrHull f → EuclideanSpace ℝ (Fin d))
    (hJcont : Continuous J) (hJinj : Function.Injective J)
    (htransport : HasLocalAmbientCarrierTransport f J) : r < d := by
  have hle : r ≤ d := by
    simpa using rank_le_finrank_of_hull_embedding hf htb hind hlam hJcont hJinj
  apply lt_of_le_of_ne hle
  intro hrd
  subst r
  exact false_of_full_independent_frequencies_of_local_ambient_transport
    hf htb hind hlam hd J hJcont hJinj htransport

/-- Finitely indexed family form of the strict autonomous-transport rank law. -/
theorem independent_family_card_lt_of_local_ambient_transport
    (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hind : LinearIndependent ℚ lam)
    (hlam : ∀ j, IsBohrHullFrequency f (lam j))
    {d : ℕ} (hd : 0 < d)
    (J : BohrHull f → EuclideanSpace ℝ (Fin d))
    (hJcont : Continuous J) (hJinj : Function.Injective J)
    (htransport : HasLocalAmbientCarrierTransport f J) : Fintype.card ι < d := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  exact independent_frequencies_lt_of_local_ambient_transport hf htb
    (hind.comp e e.injective) (fun j => hlam (e j)) hd J hJcont hJinj htransport

end GaloisForLFunctions
