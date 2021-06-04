# Week 1:
## 16/03/2021

Plan for PhD First year:
1. Literature review, gather background and summarise what they did and what i understand (around 1 month)
	A. quickly look at Abstract + (intro + conclusion) to pick papers 
2. Some formalisation and read at the same time

Main things to read about Lambda calculus for now:
1. Intersection types
2. Y.Forster’s formalisation in Coq 
3. B. Accattoli high level intro 

Plan for this week:
1. Read abstracts of all references in the proposal and highlighting and summarising 
2. Read the whole [1] and summarise 
3. Highlight the references in the references 

Extra regular meetings:
1. Reading group: Tuesday 2pm programming languages and verification; Friday 1:45pm concurrency 
2. Cogent meetings: Wednesday 10am

Courses to take during PhD: (pick ~one)
1. T3 Isabelle course 
2. 3161 semantics and languages 
3. T2 June 3141 Haskell  (functional programming).


# Week 2:
## 23/03/2021

Before the meeting: meeting with Michael for 20 mins 

TODO: 
1. Email Vincent my new email address
2. Reading group paper 
3. To create folders and upload summaries and PDFs of references onto the gitrepo summaries-ZhuoZoeyChen
4. Check Student ID

Readings:
1. Evaluation context 
2. Contextual equivalence 
3. Operational semantics 

Plan:
1. Continue reading and summarising paper [1] and look up concepts that I don’t know 
2. Summary: why reading; highlighting; summarising
3. Browse: look at Y Foster; look at other papers  

# Week 3:
## 30/03/2021

Pre-meeting:
1. Endnote?

Readings from last week:
1. Evaluation context:  

TODO:
1. read explicit substitution and write summary 
2. keep writing summary for the last paper 
3. type up notes
4. go through the book about writing  


# Week 4:
## 04/04/2021

TODO:
1. rewrite summaries (remove this paper..)
2. ES why include typed lambda calculus 
3. look at yannick's paper 
	A. decidability v.s. cost model 
	B. call-by-push-value 
	C. https://www.ps.uni-saarland.de/~forster/ 
	D. get some high level understanding of C 
	E. The Weak Call-by-Value -Calculus Is Reasonable for Both Time and Space 
	F. also have a look at D's Coq formalisation 
	G. think about what we could be doing (what's open from E)
	H. Towards a library of formalised undecidable problems in Coq: The undecidability of intuitionistic linear logic
	I. https://www.youtube.com/watch?v=myMM7FuaJY4&t=1613s

# Week 5:
## 14/04/2021

Pre-meeting: 
1. Isabelle or HOL4 or Coq? - unknown 
2. Meeting with Carroll? - wait for a few more weeks 
3. Scholarship is not taxable 
4. Progress: Yannick's papers + talk; GSOE talks 

Minutes:
1. Talked about saarland university 
2. Went through (quickly) The Weak Call-by-Value -Calculus Is Reasonable for Both Time and Space 
3. Went through the formalisation of 2 quickly 
4. Talked about Yannick's Church's thesis talk 
5. Looked at (abstract+conclusion of) Verified Programming of Turing Machines in Coq 

TODO:
1. Go through the book about writing;
2. Read Verified Programming of Turing Machines in Coq 
3. The Weak Call-by-Value -Calculus Is Reasonable for Both Time and Space 
	A. what is the definition of size (time and space) in TM and LC
	B. what do they prove at the end
	C. check if he proves everything in paper in Coq (what's the gap btw paper and formalisation)
4. Check Yannick's recent papers to see what's open and what's been done 
5. Check his git repo and download the coq version he is using 
6. Check out types, linear types, types and complexity (just browse) 

Next week:
1. maybe contact yannick next week 
2. New topics: types, linear types, types and complexity 
3. Work through some Coq formalisation together 

# Week 6:
## 21/04/2021

Pre-meeting: 
1. Went through the elements of style
2. wrote summary for Verified Programming of Turing Machines in Coq 
3.  The Weak Call-by-Value -Calculus Is Reasonable for Both Time and Space 
	A. /
	B. Mechanised results of the abstract machines (substitution machine and heap machine)
	C. Not the simulation of L 
4. Looked linear logic and linear types; confused about linear logic 
5. Got the git repo but a bit confused about the additional package 

TODO:
1. Check out the newer versions of the elements of style 
2. https://github.com/uds-psl/time-invariance-thesis-for-L 
	A. get OPAM, Coq and the packages 
	B. work through the proof slowly 
	C. maybe formalise something in HOL4 based on their coq proof 
3. Look at formalisations 
	A. try to get a high-level overview of what is proven and what remains open
	B. what helpful libraries are there in each ITP (HOL4, Isabelle/HOL, Coq)
		a. write diagrams/tables/... of what is in which ITP 
		b. what is proven
		c. what remains open
		d. is anything reusable to solve open problems 
	C. What will be a good problem to start to formalise?
4. [extra] Things might be relevant to complexity/compilation/... problems: (label them as easy to hard; easy - 0.5yrs, hard - 2yrs)
	A. Substitution machine
	B. Intersection types; David Sands. 
	C. Linear logic (just to get high-level understanding). 
	D. Denotational semantics (?)
	E. Call by push value (Paul Levy)

# Week 7:
## 03/05/2021 

More HW:
1. Look at the lecture slides up to (including) week5, maybe videos 
2. http://www.cse.unsw.edu.au/~cs3161/20T3/Week%2005/1Mon/Code.html 
3. check out the haskell code 
4. formalise the syntax of the language, M machine and C machine in HOL4

# Week 9
## 18/05/2021 

TODO:
1. apply for the laptop 
2. M C machine formalisation 

Engaging with Research End-Users survey 

# Week 10
## 25/05/2021 

TODO:
1. Software foundation (don’t spend too much time)
2. Watch lectures/do some exercises 
3. (IMPORTANT) M C machine formalisation, compiler, decompiler 
4. Types and programming language 

Left from previous weeks:
1. Check out the newer versions of the elements of style 
2. https://github.com/uds-psl/time-invariance-thesis-for-L 
	A. get OPAM, Coq and the packages 
	B. work through the proof slowly 
	C. maybe formalise something in HOL4 based on their coq proof 
3. Look at formalisations 
	A. try to get a high-level overview of what is proven and what remains open
	B. what helpful libraries are there in each ITP (HOL4, Isabelle/HOL, Coq)
		a. write diagrams/tables/... of what is in which ITP 
		b. what is proven
		c. what remains open
		d. is anything reusable to solve open problems 
	C. What will be a good problem to start to formalise?
4. [extra] Things might be relevant to complexity/compilation/... problems: (label them as easy to hard; easy - 0.5yrs, hard - 2yrs)
	A. Substitution machine
	B. Intersection types; David Sands. 
	C. Linear logic (just to get high-level understanding). 
	D. Denotational semantics (?)
	E. Call by push value (Paul Levy)

# Week 11
## 01/06/2021

Meeting postponed to next week. 

TODOs:
1. finish the reading group paper (abstracting abstract machines) 
2. read next week's reading group's paper 
3. Practical Foundations for Programming Languages
