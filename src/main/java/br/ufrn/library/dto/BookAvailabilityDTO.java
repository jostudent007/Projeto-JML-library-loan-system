package br.ufrn.library.dto;

import br.ufrn.library.model.Book;
import br.ufrn.library.model.DigitalBook;
import br.ufrn.library.model.PhysicalBook;

public class BookAvailabilityDTO {

    private /*@ spec_public @*/ final String isbn;
    private /*@ spec_public @*/ final String title;
    private /*@ spec_public @*/ final String author;
    private /*@ spec_public @*/ final String type;
    private /*@ spec_public @*/ final String availability;

    /*@ public behavior
      @   requires book != null;
      @   requires book instanceof PhysicalBook ==> 
      @      ((PhysicalBook)book).totalCopies >= 0 &&
      @      ((PhysicalBook)book).availableCopies >= 0 &&
      @      ((PhysicalBook)book).availableCopies <= ((PhysicalBook)book).totalCopies;
      @*/
    public BookAvailabilityDTO(Book book) {
        this.isbn = book.getIsbn();
        this.title = book.getTitle();
        this.author = book.getAuthor();

        if (book instanceof PhysicalBook) {
            PhysicalBook physicalBook = (PhysicalBook) book;
            this.type = "Físico";
            this.availability =
                physicalBook.getAvailableCopies() + " / " + physicalBook.getTotalCopies();

        } else if (book instanceof DigitalBook) {
            this.type = "Digital";
            this.availability = "Sempre disponível";
        } else {
            this.type = "Unknown";
            this.availability = "N/A";
        }
    }

    /*@ pure @*/ public String getIsbn() { return isbn; }
    /*@ pure @*/ public String getTitle() { return title; }
    /*@ pure @*/ public String getAuthor() { return author; }
    /*@ pure @*/ public String getType() { return type; }
    /*@ pure @*/ public String getAvailability() { return availability; }
}
