sig Author {}
sig Member {}
sig Librarian extends Member {}

sig Book {
    authors: some Author,
    borrower: one Member
}
one sig Library {
    catalog: set Book,
    members: set Member
}
fact LibraryRules {
    one Librarian
    all b: Library.catalog | b.borrower in Library.members
}

pred show {
    some Library.catalog
}


run show for 4