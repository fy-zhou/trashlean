import Mathlib

/-!
# TRASH-0001, Part III: The Academic Life Model

A fictional event-sourced model of researchers, manuscripts, experiments,
independent referees, editorial decisions, and private schedules.

Unlike the polynomial toy representation, the public outcome is reconstructed
from a causal certificate in an event history. No inequality between CCFA
and CCBB is postulated. The numerical thresholds below are model parameters,
not actual CCF or conference requirements.
-/

namespace Trashlean.Academic.Life

open scoped BigOperators

inductive Venue where
  | A | B
  deriving DecidableEq, Repr

def minEvidence : Venue → ℕ
  | .A => 3
  | .B => 1

def minEffort : Venue → ℕ
  | .A => 3
  | .B => 1

structure Submission where
  paper : ℕ
  author : ℕ
  affiliation : ℕ
  version : ℕ
  time : ℕ
  experiments : ℕ
  effortSlots : Finset ℕ
  deriving DecidableEq

structure Report where
  paper : ℕ
  version : ℕ
  affiliation : ℕ
  time : ℕ
  score : ℕ
  reproducible : Bool
  deriving DecidableEq

structure Decision where
  paper : ℕ
  version : ℕ
  time : ℕ
  quorum : ℕ
  cutoff : ℕ
  accepted : Bool
  deriving DecidableEq

inductive AcademicEvent where
  | submission (data : Submission)
  | review (reviewer : ℕ) (data : Report)
  | decision (data : Decision)
  deriving DecidableEq

def academicTime : AcademicEvent → ℕ
  | .submission s => s.time
  | .review _ r => r.time
  | .decision d => d.time

structure Episode where
  start : ℕ
  duration : ℕ
  participants : Finset ℕ
  consenting : Finset ℕ
  deriving DecidableEq

inductive Event where
  | academic (venue : Venue) (payload : AcademicEvent)
  | episode (data : Episode)
  deriving DecidableEq

abbrev History := List Event
abbrev PublicLog := List (Venue × AcademicEvent)

/-! ## Observation and causal certification -/

def publicTrace : History → PublicLog
  | [] => []
  | .academic v e :: rest => (v, e) :: publicTrace rest
  | .episode _ :: rest => publicTrace rest

/-- The lexical joke is an operation on labels, not on people or events. -/
def lexicalRewrite (word : List Char) : List Char :=
  word.map (fun c => if c = 'F' then 'B' else c)

theorem lexical_derivation :
    lexicalRewrite "CCFB".toList = "CCBB".toList := by decide

def privateTrace : History → List Episode
  | [] => []
  | .academic _ _ :: rest => privateTrace rest
  | .episode e :: rest => e :: privateTrace rest

def restorePublic (log : PublicLog) : History :=
  log.map fun p => Event.academic p.1 p.2

def embed (v : Venue) (log : List AcademicEvent) : History :=
  restorePublic (log.map fun e => (v, e))

def privateSuffix (sessions : List Episode) : History :=
  sessions.map Event.episode

@[simp] theorem public_append (h k : History) :
    publicTrace (h ++ k) = publicTrace h ++ publicTrace k := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [publicTrace, ih]

@[simp] theorem public_restore (log : PublicLog) :
    publicTrace (restorePublic log) = log := by
  induction log with
  | nil => rfl
  | cons p log ih =>
      rcases p with ⟨v, e⟩
      change (v, e) :: publicTrace (restorePublic log) = (v, e) :: log
      rw [ih]

@[simp] theorem public_private (sessions : List Episode) :
    publicTrace (privateSuffix sessions) = [] := by
  induction sessions with
  | nil => rfl
  | cons e es ih => simpa [privateSuffix, publicTrace] using ih

@[simp] theorem private_append (h k : History) :
    privateTrace (h ++ k) = privateTrace h ++ privateTrace k := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [privateTrace, ih]

@[simp] theorem private_restore (log : PublicLog) :
    privateTrace (restorePublic log) = [] := by
  induction log with
  | nil => rfl
  | cons p log ih =>
      rcases p with ⟨v, e⟩
      change privateTrace (restorePublic log) = []
      exact ih

@[simp] theorem private_private (sessions : List Episode) :
    privateTrace (privateSuffix sessions) = sessions := by
  induction sessions with
  | nil => rfl
  | cons e es ih =>
      change e :: privateTrace (privateSuffix es) = e :: es
      rw [ih]

/-- A certificate requires a causally ordered submission, independently
identified referees, evidence and effort, sufficient scores, and a decision.
The witness is data, while existence of a witness is a proposition. -/
structure Certificate (log : PublicLog) (v : Venue) (paper : ℕ) where
  submission : Submission
  decision : Decision
  reviewers : Finset ℕ
  reports : ℕ → Report
  submitted : (v, .submission submission) ∈ log
  decided : (v, .decision decision) ∈ log
  submissionPaper : submission.paper = paper
  decisionPaper : decision.paper = paper
  sameVersion : decision.version = submission.version
  decisionAccepted : decision.accepted = true
  evidenceThreshold : minEvidence v ≤ submission.experiments
  effortThreshold : minEffort v ≤ submission.effortSlots.card
  effortBeforeSubmission : ∀ t ∈ submission.effortSlots, t < submission.time
  quorumMinimum : 2 ≤ decision.quorum
  enoughReferees : decision.quorum ≤ reviewers.card
  reviewValidity : ∀ r ∈ reviewers,
    (v, .review r (reports r)) ∈ log ∧
    r ≠ submission.author ∧
    (reports r).affiliation ≠ submission.affiliation ∧
    (reports r).paper = paper ∧
    (reports r).version = submission.version ∧
    submission.time < (reports r).time ∧
    (reports r).time < decision.time ∧
    (reports r).reproducible = true ∧
    (reports r).score ≤ 10
  collectiveThreshold :
    reviewers.card * decision.cutoff ≤ ∑ r ∈ reviewers, (reports r).score

def Certified (h : History) (v : Venue) (p : ℕ) : Prop :=
  Nonempty (Certificate (publicTrace h) v p)

def CCFA (h : History) : Prop := ∃ p, Certified h .A p
def CCFB (h : History) : Prop := ∃ p, Certified h .B p

/-- An episode is an abstract record of consensual adult intimate activity.
Participant identifiers range over an assumed adult population.
No publication or academic category enters its validity conditions. -/
def validEpisode (e : Episode) : Prop :=
  0 < e.duration ∧ 2 ≤ e.participants.card ∧ e.consenting = e.participants

def CCBB (h : History) : Prop :=
  ∃ e ∈ privateTrace h, validEpisode e

theorem no_private_in_public (log : PublicLog) :
    ¬ CCBB (restorePublic log) := by
  simp [CCBB]

theorem no_certificate_in_empty_public {h : History}
    (he : publicTrace h = []) (v : Venue) (p : ℕ) :
    ¬ Certified h v p := by
  rintro ⟨c⟩
  exact (List.ne_nil_of_mem c.submitted) he

theorem certification_observational {h k : History}
    (eq : publicTrace h = publicTrace k) (v : Venue) (p : ℕ) :
    Certified h v p ↔ Certified k v p := by
  unfold Certified
  rw [eq]

theorem private_noninterference (h : History) (sessions : List Episode)
    (v : Venue) (p : ℕ) :
    Certified (h ++ privateSuffix sessions) v p ↔ Certified h v p := by
  apply certification_observational
  simp

theorem private_only_no_A (sessions : List Episode) :
    ¬ CCFA (privateSuffix sessions) := by
  rintro ⟨p, hp⟩
  exact no_certificate_in_empty_public (public_private sessions) .A p hp

theorem private_only_no_B (sessions : List Episode) :
    ¬ CCFB (privateSuffix sessions) := by
  rintro ⟨p, hp⟩
  exact no_certificate_in_empty_public (public_private sessions) .B p hp

/-! ## Quotient semantics and an observational universal property -/

def observationSetoid : Setoid History where
  r h k := publicTrace h = publicTrace k
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-- The quotient by observational equivalence is the actual public log. -/
def observationQuotientEquiv : Quotient observationSetoid ≃ PublicLog where
  toFun := Quotient.lift publicTrace (fun _ _ h => h)
  invFun l := Quotient.mk observationSetoid (restorePublic l)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro h
    apply Quotient.sound
    change publicTrace (restorePublic (publicTrace h)) = publicTrace h
    exact public_restore _
  right_inv := public_restore

/-- Every observer invariant under the observational equivalence has a
unique factorization through the public log. This is a universal property,
not a particular hand-chosen scoring function. -/
theorem universal_public_observer {Y : Type*} (f : History → Y)
    (invariant : ∀ h k, publicTrace h = publicTrace k → f h = f k) :
    ∃! g : PublicLog → Y, ∀ h, g (publicTrace h) = f h := by
  refine ⟨fun l => f (restorePublic l), ?_, ?_⟩
  · intro h
    apply invariant
    exact public_restore _
  · intro g hg
    funext l
    simpa using hg (restorePublic l)

theorem observer_private_noninterference {Y : Type*} (f : History → Y)
    (invariant : ∀ h k, publicTrace h = publicTrace k → f h = f k)
    (h : History) (sessions : List Episode) :
    f (h ++ privateSuffix sessions) = f h := by
  apply invariant
  simp

/-! ## Finite-resource constraints -/

/-- A private schedule occupies a finite collection of discrete time slots. -/
def occupied (e : Episode) : Finset ℕ :=
  Finset.Ico e.start (e.start + e.duration)

/-- Disjoint allocations inside a finite horizon obey a conservation bound. -/
theorem finite_time_budget (research leisure : Finset ℕ) (horizon : ℕ)
    (hr : research ⊆ Finset.range horizon)
    (hl : leisure ⊆ Finset.range horizon)
    (disj : Disjoint research leisure) :
    research.card + leisure.card ≤ horizon := by
  have hu : research ∪ leisure ⊆ Finset.range horizon := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · exact hr h
    · exact hl h
  have hc := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint disj, Finset.card_range] at hc
  exact hc

/-- A certified research outcome imposes a lower bound on its research
allocation; the remaining private allocation cannot violate the horizon. -/
theorem certified_budget {log : PublicLog} {v : Venue} {p : ℕ}
    (c : Certificate log v p) (leisure : Finset ℕ) (horizon : ℕ)
    (hr : c.submission.effortSlots ⊆ Finset.range horizon)
    (hl : leisure ⊆ Finset.range horizon)
    (disj : Disjoint c.submission.effortSlots leisure) :
    minEffort v + leisure.card ≤ horizon := by
  have h := finite_time_budget c.submission.effortSlots leisure horizon hr hl disj
  exact (Nat.add_le_add_right c.effortThreshold _).trans h

/-! ## Nonvacuity: explicit causal histories -/

def exampleSubmission : Submission :=
  ⟨0, 0, 0, 1, 4, 3, {0, 1, 2}⟩

def exampleReport (r : ℕ) : Report :=
  ⟨0, 1, r, 4 + r, 9, true⟩

def exampleDecision : Decision :=
  ⟨0, 1, 7, 2, 8, true⟩

def exampleLog : List AcademicEvent :=
  [.submission exampleSubmission,
   .review 1 (exampleReport 1),
   .review 2 (exampleReport 2),
   .decision exampleDecision]

def exampleCertificate (v : Venue) :
    Certificate (publicTrace (embed v exampleLog)) v 0 where
  submission := exampleSubmission
  decision := exampleDecision
  reviewers := {1, 2}
  reports := exampleReport
  submitted := by simp [embed, exampleLog]
  decided := by simp [embed, exampleLog]
  submissionPaper := rfl
  decisionPaper := rfl
  sameVersion := rfl
  decisionAccepted := rfl
  evidenceThreshold := by cases v <;> decide
  effortThreshold := by cases v <;> decide
  effortBeforeSubmission := by
    intro t ht
    simp [exampleSubmission] at ht
    rcases ht with h | h | h <;> subst t <;> decide
  quorumMinimum := by decide
  enoughReferees := by decide
  reviewValidity := by
    intro r hr
    have h : r = 1 ∨ r = 2 := by simpa using hr
    rcases h with rfl | rfl <;>
      norm_num [embed, exampleLog, exampleSubmission, exampleDecision, exampleReport]
  collectiveThreshold := by decide

theorem A_exists : CCFA (embed .A exampleLog) :=
  ⟨0, ⟨exampleCertificate .A⟩⟩

theorem B_exists : CCFB (embed .B exampleLog) :=
  ⟨0, ⟨exampleCertificate .B⟩⟩

def exampleEpisode : Episode :=
  ⟨10, 2, {0, 1}, {0, 1}⟩

theorem exampleEpisode_valid : validEpisode exampleEpisode := by
  unfold validEpisode
  decide

theorem BB_exists : CCBB (privateSuffix [exampleEpisode]) := by
  exact ⟨exampleEpisode, by simp, exampleEpisode_valid⟩

theorem BB_after_public (log : PublicLog) :
    CCBB (restorePublic log ++ privateSuffix [exampleEpisode]) := by
  exact ⟨exampleEpisode, by simp, exampleEpisode_valid⟩

theorem A_only : CCFA (embed .A exampleLog) ∧ ¬ CCBB (embed .A exampleLog) :=
  ⟨A_exists, no_private_in_public _⟩

theorem B_only : CCFB (embed .B exampleLog) ∧ ¬ CCBB (embed .B exampleLog) :=
  ⟨B_exists, no_private_in_public _⟩

theorem BB_only :
    CCBB (privateSuffix [exampleEpisode]) ∧
    ¬ CCFA (privateSuffix [exampleEpisode]) ∧
    ¬ CCFB (privateSuffix [exampleEpisode]) :=
  ⟨BB_exists, private_only_no_A _, private_only_no_B _⟩

/-- The outcome predicates are not mutually exclusive. -/
theorem coexistence :
    CCFA (embed .A exampleLog ++ privateSuffix [exampleEpisode]) ∧
      CCBB (embed .A exampleLog ++ privateSuffix [exampleEpisode]) :=
  ⟨⟨0, (private_noninterference _ _ _ _).mpr ⟨exampleCertificate .A⟩⟩,
    BB_after_public _⟩

theorem neither : ¬ CCFA [] ∧ ¬ CCBB [] := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩
    exact no_certificate_in_empty_public rfl .A p hp
  · simp [CCBB, privateTrace]

theorem CCFA_ne_CCBB : CCFA ≠ CCBB := by
  intro h
  exact A_only.2 (h ▸ A_only.1)

theorem CCFB_ne_CCBB : CCFB ≠ CCBB := by
  intro h
  exact B_only.2 (h ▸ B_only.1)

/-- The lexical derivation does not imply either semantic inclusion. -/
theorem semantic_independence :
    (¬ ∀ h, CCFB h → CCBB h) ∧ (¬ ∀ h, CCBB h → CCFB h) := by
  constructor
  · intro h
    exact B_only.2 (h _ B_only.1)
  · intro h
    exact BB_only.2.2 (h _ BB_only.1)

theorem life_model_obstruction :
    CCFA ≠ CCBB ∧ CCFB ≠ CCBB ∧
    (∃ h, CCFA h ∧ ¬ CCBB h) ∧
    (∃ h, CCBB h ∧ ¬ CCFA h) ∧
    (∃ h, CCFA h ∧ CCBB h) ∧
    (∃ h, ¬ CCFA h ∧ ¬ CCBB h) ∧
    (¬ ∀ h, CCFB h → CCBB h) ∧
    (¬ ∀ h, CCBB h → CCFB h) := by
  exact ⟨CCFA_ne_CCBB, CCFB_ne_CCBB,
    ⟨_, A_only⟩, ⟨_, BB_only.1, BB_only.2.1⟩,
    ⟨_, coexistence⟩, ⟨_, neither⟩,
    semantic_independence.1, semantic_independence.2⟩

#print axioms life_model_obstruction
#print axioms universal_public_observer

end Trashlean.Academic.Life
